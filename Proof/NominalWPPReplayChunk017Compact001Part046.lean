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
import NominalWPPReplayChunk017Compact001Part045

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

noncomputable def g_hncodeprednonemptyminimalndv
    (z : Var) (v : Var) (u : Var) (A : Class) (X : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_X_u : u ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_u_v : u ≠ v) (dv_u_z : u ≠ z) (dv_v_z : v ≠ z) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wrex u X (syn_wral z X (.imp (syn_wbr (.cv z) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv z) (.cv u)))))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ X.fv
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_ne_v : a ≠ v := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_ne_a : v ≠ a :=
    Ne.symm fresh_a_ne_v
  have fresh_a_ne_u : a ≠ u := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_a : u ≠ a :=
    Ne.symm fresh_a_ne_u
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_z : x ≠ z := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have dv_cache_0001 : v ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cfv (syn_c1st) (.cv v))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((syn_cfv (syn_c1st) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_chncodepredends A X v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_X, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((syn_chncodepredends A X v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_not_X, fresh_a_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ a from (by exact fresh_x_ne_a))
  have dv_cache_0007 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0010 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0011 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : u ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show u ≠ z from (by exact dv_u_z))
  have dv_cache_0016 : u ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show u ≠ a from (by exact fresh_u_ne_a))
  have dv_cache_0017 : v ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show v ≠ z from (by exact dv_v_z))
  have dv_cache_0018 : v ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show v ≠ a from (by exact fresh_v_ne_a))
  have dv_cache_0019 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0020 : z ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show z ≠ a from (by exact fresh_z_ne_a))
  have dv_cache_0021 : u ∉ ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, dv_X_u, dv_u_v, fresh_u_ne_x, fresh_u_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((syn_wrex u X (syn_wral z X (.imp (syn_wbr (.cv z) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv z) (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, fresh_x_ne_z, fresh_x_ne_u, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_X, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0001 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0000
  have p0002 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0001
  have p0003 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0004 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0003
  have p0005 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0004
  have p0006 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) X (syn_chwcn A) (.cv v) p0002 p0005
  have p0007 :=
    @g_hwcnwendv v A dv_cache_0001
  have p0008 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv v) (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v))) p0006 p0007
  have p0009 :=
    @g_wefrndv (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v))
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cfound) (syn_cfv (syn_c2nd) (.cv v))) p0008 p0009
  have p0011 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0012 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0011
  have p0013 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (.classMem X (syn_cvv)) p0012
  have p0014 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0015 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0014
  have p0016 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (.classMem X (syn_cvv)) p0015
  have p0017 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (.classMem X (syn_cvv)) p0013 p0016
  have p0018 :=
    @g_hncodepredendsexg v A X dv_cache_0001
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_chncodepredends A X v) (syn_cvv)) p0017 p0018
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0021 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0020
  have p0022 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0021
  have p0023 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0024 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0023
  have p0025 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0024
  have p0026 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) X (syn_chwcn A) (.cv v) p0022 p0025
  have p0027 :=
    @g_hncodepredendsssndv v A X dv_cache_0001
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv v) (syn_chwcn A)) (syn_wss (syn_chncodepredends A X v) (syn_cfv (syn_c2nd) (.cv v))) p0026 p0027
  have p0029 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0030 :=
    @g_frd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) x a (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v)) (syn_cvv) (syn_chncodepredends A X v) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0010 p0019 p0028 p0029
  have p0031 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))
  have p0032 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))) p0031
  have p0033 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))
  have p0034 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0035 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0034
  have p0036 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0035
  have p0037 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0038 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0037
  have p0039 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0038
  have p0040 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) X (syn_chwcn A) (.cv v) p0036 p0039
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv v) (syn_chwcn A)) p0033 p0040
  have p0042 :=
    @g_hncodepredendsmemndv x v u A X dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv v) (syn_chwcn A)) (syn_wb (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0041 p0042
  have p0044 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0032 p0043
  have p0045 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0044
  have p0046 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0047 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X) p0046
  have p0048 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))
  have p0049 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0050 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0049
  have p0051 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (.classMem X (syn_cvv)) p0050
  have p0052 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) p0048 p0051
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem A (syn_cvv)) p0047 p0052
  have p0054 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0055 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X) p0054
  have p0056 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))
  have p0057 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0058 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0057
  have p0059 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0058
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) p0056 p0059
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (syn_wss X (syn_chwcn A)) p0055 p0060
  have p0062 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0063 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X) p0062
  have p0064 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))
  have p0065 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0066 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0065
  have p0067 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0066
  have p0068 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0069 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0068
  have p0070 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0069
  have p0071 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) X (syn_chwcn A) (.cv v) p0067 p0070
  have p0072 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv v) (syn_chwcn A)) p0064 p0071
  have p0073 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv v) (syn_chwcn A)) p0063 p0072
  have p0074 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0061 p0073
  have p0075 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0053 p0074
  have p0076 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0077 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X) p0076
  have p0078 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))
  have p0079 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))) p0078
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv x) (syn_chncodepredends A X v)) p0077 p0079
  have p0081 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0082 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X) p0081
  have p0083 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0084 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0082 p0083
  have p0085 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0080 p0084
  have p0086 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0087 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X) p0086
  have p0088 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))
  have p0089 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))) p0088
  have p0090 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))) p0087 p0089
  have p0091 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))) p0085 p0090
  have p0092 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x))))) p0075 p0091
  have p0093 :=
    @g_hncodepredrepminimalndv x z a v u A X dv_cache_0007 dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0006 dv_cache_0020
  have p0094 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (syn_wral z X (.imp (syn_wbr (.cv z) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv z) (.cv u)))) p0092 p0093
  have p0095 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) (syn_wral z X (.imp (syn_wbr (.cv z) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv z) (.cv u)))) p0094
  have p0096 :=
    @g_reximdva (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) (syn_wral z X (.imp (syn_wbr (.cv z) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv z) (.cv u)))) u X dv_cache_0021 p0095
  have p0097 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wrex u X (syn_wral z X (.imp (syn_wbr (.cv z) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv z) (.cv u))))) p0045 p0096
  have p0098_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wrex x (syn_chncodepredends A X v) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wne syn_chncodepredends syn_cuni syn_wex syn_cima syn_wrex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_c2nd syn_copab syn_chncodepredinputs syn_cin syn_cxp syn_csn syn_cpw1 syn_cfv syn_cio syn_c0 syn_cdif syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0030
  have p0098 :=
    @g_rexlimddv (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wral a (syn_chncodepredends A X v) (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv a) (.cv x)))) (syn_wrex u X (syn_wral z X (.imp (syn_wbr (.cv z) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv z) (.cv u))))) x (syn_chncodepredends A X v) dv_cache_0022 dv_cache_0023 p0098_e00_recanon p0097
  exact p0098

#print axioms g_hncodeprednonemptyminimalndv

end NFChoice.DirectNominalPrf.WPPReplay
