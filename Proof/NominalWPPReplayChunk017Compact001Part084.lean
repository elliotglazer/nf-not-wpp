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
import NominalWPPReplayChunk017Compact001Part083

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

noncomputable def g_hninjraisedselfcutcmpndv
    (x : Var) (u : Var) (A : Class) (f : Var) (dv_A_f : f ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) (dv_u_x : u ≠ x) (hyp_hninjraisedselfcutcmpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({f} : Finset Var)
  let r : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_u : r ≠ u := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_r : u ≠ r :=
    Ne.symm fresh_r_ne_u
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_f : r ≠ f := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_r : f ≠ r :=
    Ne.symm fresh_r_ne_f
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_ne_x : s ≠ x := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_s : x ≠ s :=
    Ne.symm fresh_s_ne_x
  have fresh_s_ne_u : s ≠ u := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_s : u ≠ s :=
    Ne.symm fresh_s_ne_u
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_ne_f : s ≠ f := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_s : f ≠ s :=
    Ne.symm fresh_s_ne_f
  have fresh_r_ne_s : r ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_r : s ≠ r :=
    Ne.symm fresh_r_ne_s
  have dv_cache_0001 : r ∉ ((syn_chncodecmpset A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({r} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show r ∉ (A).fv from (by exact fresh_r_not_A))))))
  have dv_cache_0003 : s ∉ ((syn_clnqord (.cv r) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, fresh_s_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0010 : f ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ s from (by exact fresh_f_ne_s))
  have dv_cache_0011 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0012 : f ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show f ≠ x from (by exact dv_f_x))
  have dv_cache_0013 : r ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show r ≠ s from (by exact fresh_r_ne_s))
  have dv_cache_0014 : r ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show r ≠ u from (by exact fresh_r_ne_u))
  have dv_cache_0015 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0016 : s ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show s ≠ u from (by exact fresh_s_ne_u))
  have dv_cache_0017 : s ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show s ≠ x from (by exact fresh_s_ne_x))
  have dv_cache_0018 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0019 : s ∉ ((syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, fresh_s_ne_u, fresh_s_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : s ∉ ((syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, fresh_s_ne_f, fresh_s_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : r ∉ ((syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_u, fresh_r_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : r ∉ ((syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hncodecmpsetexg A
  have p0001 :=
    Nominal.mp hyp_hninjraisedselfcutcmpndv_1 p0000
  have p0002 :=
    @g_isset r (syn_chncodecmpset A) dv_cache_0001
  have p0003 :=
    @g_mpbi (.classMem (syn_chncodecmpset A) (syn_cvv)) (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A))) p0001 p0002
  have p0004 :=
    @g_a1i (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) p0003
  have p0005 :=
    @g_hncodecmpsetexg A
  have p0006 :=
    Nominal.mp hyp_hninjraisedselfcutcmpndv_1 p0005
  have p0007 :=
    @g_a1i (.classMem (syn_chncodecmpset A) (syn_cvv)) (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))) p0006
  have p0008 :=
    @g_simpr (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0009 :=
    @g_eleq1d (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))) (.cv r) (syn_chncodecmpset A) (syn_cvv) p0008
  have p0010 :=
    @g_mpbird (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0007 p0009
  have p0011 :=
    @g_hwcnex A hyp_hninjraisedselfcutcmpndv_1
  have p0012 :=
    @g_a1i (.classMem (syn_chwcn A) (syn_cvv)) (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))) p0011
  have p0013 :=
    @g_jca (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_lnqordexg (syn_chwcn A) (.cv r) dv_cache_0002
  have p0015 :=
    @g_syl (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_isset s (syn_clnqord (.cv r) (syn_chwcn A)) dv_cache_0003
  have p0017 :=
    @g_a1i (syn_wb (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv)) (syn_wex s (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))))) (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))) p0016
  have p0018 :=
    @g_mpbid (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv)) (syn_wex s (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))) p0015 p0017
  have p0019 :=
    @g_hninjraisedselfcutalldndv x u A f s r dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 hyp_hninjraisedselfcutcmpndv_1
  have p0020 :=
    @g_anassrs (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))) (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))) p0019
  have p0021 :=
    @g_exlimddv (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A))) (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A))) (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))) s dv_cache_0019 dv_cache_0020 p0018 p0020
  have p0022 :=
    @g_exlimddv (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))) r dv_cache_0021 dv_cache_0022 p0004 p0021
  exact p0022

noncomputable def g_hnselfcutnoex2ndv
    (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) :
    Nominal.NPrf (.neg (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutcodeselfnoisondv x u A dv_cache_0001
  have p0001 :=
    @g_nrexdv (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0002 p0000
  have p0002 :=
    @g_nrex (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) u (syn_chwcn A) p0001
  exact p0002

noncomputable def g_hncardtc2nodomndv
    (A : Class) (hyp_hncardtc2nodomndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.neg (syn_wbr (syn_chncard A) (syn_clec) (syn_ctc (syn_ctc (syn_cnc A))))) := by
  let proofSupport : Finset Var := A.fv
  let f : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (h)
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_f_ne_u : f ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_f : u ≠ f :=
    Ne.symm fresh_f_ne_u
  have fresh_f_ne_x : f ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_f : x ≠ f :=
    Ne.symm fresh_f_ne_x
  have fresh_u_ne_x : u ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have dv_cache_0001 : u ∉ ((syn_cpw1 (syn_cpw1 A))).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cpw1 (syn_cpw1 A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0004 : f ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0008 : f ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0009 : f ∉ ((syn_chnord A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : f ∉ ((syn_cpw1 (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnselfcutnoex2ndv x u (syn_cpw1 (syn_cpw1 A)) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_hninjraisedselfcutcmpndv x u A f dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0003 hyp_hncardtc2nodomndv_1
  have p0002 :=
    @g_con3i (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))) p0001
  have p0003 :=
    Nominal.mp p0000 p0002
  have p0004 :=
    @g_nex (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) f p0003
  have p0005 :=
    @g_hnordex A hyp_hncardtc2nodomndv_1
  have p0006 :=
    @g_pw1ex A hyp_hncardtc2nodomndv_1
  have p0007 :=
    @g_pw1ex (syn_cpw1 A) p0006
  have p0008 :=
    @g_nclenc (syn_chnord A) (syn_cpw1 (syn_cpw1 A)) f dv_cache_0009 dv_cache_0010 p0005 p0007
  have p0009 :=
    @g_notbii (syn_wbr (syn_cnc (syn_chnord A)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 A)))) (syn_wex f (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))) p0008
  have p0010 :=
    @g_mpbir (.neg (syn_wbr (syn_cnc (syn_chnord A)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 A))))) (.neg (syn_wex f (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))))) p0004 p0009
  have p0011 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard A)))
  have p0012 :=
    @g_tc2nc A hyp_hncardtc2nodomndv_1
  have p0013 :=
    @g_breq12i (syn_chncard A) (syn_cnc (syn_chnord A)) (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) p0011 p0012
  have p0014 :=
    @g_notbii (syn_wbr (syn_chncard A) (syn_clec) (syn_ctc (syn_ctc (syn_cnc A)))) (syn_wbr (syn_cnc (syn_chnord A)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 A)))) p0013
  have p0015 :=
    @g_mpbir (.neg (syn_wbr (syn_chncard A) (syn_clec) (syn_ctc (syn_ctc (syn_cnc A))))) (.neg (syn_wbr (syn_cnc (syn_chnord A)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 A))))) p0010 p0014
  exact p0015

noncomputable def g_wppconcrete6representedmonondv
    (X : Class) (Y : Class) (hyp_wppconcrete6representedmonondv_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_wppconcrete6representedmonondv_2 : Nominal.NPrf (.classMem Y (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))))) := by
  let proofSupport : Finset Var := X.fv ∪ Y.fv
  have p0000 :=
    @g_ncelncsi X hyp_wppconcrete6representedmonondv_1
  have p0001 :=
    @g_ncelncsi Y hyp_wppconcrete6representedmonondv_2
  have p0002 :=
    @g_tc6lecan (syn_cnc X) (syn_cnc Y) p0000 p0001
  have p0003 :=
    @g_ncpw2le X Y hyp_wppconcrete6representedmonondv_1 hyp_wppconcrete6representedmonondv_2
  have p0004 :=
    @g_syl (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))) (syn_wbr (syn_cnc X) (syn_clec) (syn_cnc Y)) (syn_wbr (syn_cnc (syn_cpw (syn_cpw X))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw Y)))) p0002 p0003
  have p0005 :=
    @g_pwex X hyp_wppconcrete6representedmonondv_1
  have p0006 :=
    @g_pwex (syn_cpw X) p0005
  have p0007 :=
    @g_pwex Y hyp_wppconcrete6representedmonondv_2
  have p0008 :=
    @g_pwex (syn_cpw Y) p0007
  have p0009 :=
    @g_hnordcardnclecndv (syn_cpw (syn_cpw Y)) (syn_cpw (syn_cpw X)) p0006 p0008
  have p0010 :=
    @g_syl (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))) (syn_wbr (syn_cnc (syn_cpw (syn_cpw X))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw Y)))) (syn_wbr (syn_cnc (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw Y))))) p0004 p0009
  have p0011 :=
    @g_pwex X hyp_wppconcrete6representedmonondv_1
  have p0012 :=
    @g_pwex (syn_cpw X) p0011
  have p0013 :=
    @g_hnordex (syn_cpw (syn_cpw X)) p0012
  have p0014 :=
    @g_pwex Y hyp_wppconcrete6representedmonondv_2
  have p0015 :=
    @g_pwex (syn_cpw Y) p0014
  have p0016 :=
    @g_hnordex (syn_cpw (syn_cpw Y)) p0015
  have p0017 :=
    @g_hncardnclecndv (syn_chnord (syn_cpw (syn_cpw Y))) (syn_chnord (syn_cpw (syn_cpw X))) p0013 p0016
  have p0018 :=
    @g_syl (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))) (syn_wbr (syn_cnc (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw Y))))) (syn_wbr (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec) (syn_chncard (syn_chnord (syn_cpw (syn_cpw Y))))) p0010 p0017
  have p0019 :=
    @g_wppconcrete6fnvalndv X hyp_wppconcrete6representedmonondv_1
  have p0020 :=
    @g_wppconcrete6fnvalndv Y hyp_wppconcrete6representedmonondv_2
  have p0021 :=
    @g_breq12i (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw Y)))) (syn_clec) p0019 p0020
  have p0022 :=
    @g_biimpri (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y))))))))) (syn_wbr (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec) (syn_chncard (syn_chnord (syn_cpw (syn_cpw Y))))) p0021
  have p0023 :=
    @g_syl (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))) (syn_wbr (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec) (syn_chncard (syn_chnord (syn_cpw (syn_cpw Y))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y))))))))) p0018 p0022
  exact p0023

noncomputable def g_letc6ncrepdv
    (z : Var) (M : Class) (N : Class) (dv_M_z : z ∉ M.fv) (dv_N_z : z ∉ N.fv) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wex z (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ M.fv ∪ N.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_z : p ≠ z := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_p : z ≠ p :=
    Ne.symm fresh_p_ne_z
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_z, dv_N_z, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_wex z (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_M, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_M, fresh_p_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_letc6w6ndv M N p dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
  have p0002 :=
    @g_simpr (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))
  have p0003 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classMem (.cv p) (syn_cncs)) p0001 p0002
  have p0004 :=
    @g_elncs z (.cv p) dv_cache_0003
  have p0005 :=
    @g_biimpi (.classMem (.cv p) (syn_cncs)) (syn_wex z (.classEq (.cv p) (syn_cnc (.cv z)))) p0004
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classMem (.cv p) (syn_cncs)) (syn_wex z (.classEq (.cv p) (syn_cnc (.cv z)))) p0003 p0005
  have p0007 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))
  have p0008 :=
    @g_simpr (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))) (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p0007 p0008
  have p0010 :=
    @g_simpr (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))
  have p0011 :=
    @g_tceq (.cv p) (syn_cnc (.cv z))
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))) (.classEq (.cv p) (syn_cnc (.cv z))) (.classEq (syn_ctc (.cv p)) (syn_ctc (syn_cnc (.cv z)))) p0010 p0011
  have p0013 :=
    @g_tceq (syn_ctc (.cv p)) (syn_ctc (syn_cnc (.cv z)))
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))) (.classEq (syn_ctc (.cv p)) (syn_ctc (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (.cv p))) (syn_ctc (syn_ctc (syn_cnc (.cv z))))) p0012 p0013
  have p0015 :=
    @g_tceq (syn_ctc (syn_ctc (.cv p))) (syn_ctc (syn_ctc (syn_cnc (.cv z))))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (.cv p))) (syn_ctc (syn_ctc (syn_cnc (.cv z))))) (.classEq (syn_ctc (syn_ctc (syn_ctc (.cv p)))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))) p0014 p0015
  have p0017 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (.cv p)))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (syn_ctc (.cv p)))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))) p0016 p0017
  have p0019 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) p0018 p0019
  have p0021 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) p0020 p0021
  have p0023 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z)))) M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) p0009 p0022
  have p0024 :=
    @g_ex (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) p0023
  have p0025 :=
    @g_eximdv (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (.classEq (.cv p) (syn_cnc (.cv z))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) z dv_cache_0004 p0024
  have p0026 :=
    @g_mpd (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (syn_wex z (.classEq (.cv p) (syn_cnc (.cv z)))) (syn_wex z (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0006 p0025
  have p0027 :=
    @g_ex (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv p) (syn_cncs))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) (syn_wex z (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0026
  have p0028 :=
    @g_rexlimdva (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) (syn_wex z (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p (syn_cncs) dv_cache_0005 dv_cache_0006 p0027
  have p0029 :=
    @g_mpd (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (syn_wex z (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0000 p0028
  exact p0029

noncomputable def g_wppconcrete6tcvalncndv
     :
    Nominal.NPrf (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard (syn_c1c))))
  have p0001 :=
    @g_tceq (syn_chncard (syn_c1c)) (syn_cnc (syn_chnord (syn_c1c)))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_n_1cex
  have p0004 :=
    @g_hnordex (syn_c1c) p0003
  have p0005 :=
    @g_tcnc (syn_chnord (syn_c1c)) p0004
  have p0006 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_c1c))) (syn_ctc (syn_cnc (syn_chnord (syn_c1c)))) (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))) p0002 p0005
  have p0007 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_fveq2i (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))) (syn_cwppconcrete6fn) p0018
  have p0020 :=
    @g_n_1cex
  have p0021 :=
    @g_hnordex (syn_c1c) p0020
  have p0022 :=
    @g_pw1ex (syn_chnord (syn_c1c)) p0021
  have p0023 :=
    @g_wppconcrete6fnvalndv (syn_cpw1 (syn_chnord (syn_c1c))) p0022
  have p0024 :=
    @g_eqtri (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c))))))) p0019 p0023
  have p0025 :=
    @g_n_1cex
  have p0026 :=
    @g_hnordex (syn_c1c) p0025
  have p0027 :=
    @g_pw1ex (syn_chnord (syn_c1c)) p0026
  have p0028 :=
    @g_pwex (syn_cpw1 (syn_chnord (syn_c1c))) p0027
  have p0029 :=
    @g_pwex (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c)))) p0028
  have p0030 :=
    @g_hnordex (syn_cpw (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c))))) p0029
  have p0031 :=
    @g_hncardnc (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c))))))
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_eqeltri (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c))))))) (syn_cncs) p0024 p0032
  exact p0033

#print axioms g_wppconcrete6tcvalncndv

end NFChoice.DirectNominalPrf.WPPReplay
