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
import NominalWPPReplayChunk017Compact001Part090

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

noncomputable def g_cfbwpphwcncarrierinjndv
    (C : Class) (k : Var) (X : Class) (dv_C_k : k ∉ C.fv) (dv_X_k : k ∉ X.fv) (hyp_cfbwpphwcncarrierinjndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_cfbwpphwcncarrierinjndv_2 : Nominal.NPrf (.classMem C (syn_chwcn (syn_cpw X)))) (hyp_cfbwpphwcncarrierinjndv_3 : Nominal.NPrf (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X)))))) := by
  let proofSupport : Finset Var := C.fv ∪ ({k} : Finset Var) ∪ X.fv
  let r : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_ne_k : r ≠ k := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_r : k ≠ r :=
    Ne.symm fresh_r_ne_k
  have fresh_r_not_X : r ∉ X.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_ne_k : a ≠ k := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_a : k ≠ a :=
    Ne.symm fresh_a_ne_k
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_r_ne_a : r ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    Ne.symm fresh_r_ne_a
  have dv_cache_0001 : k ∉ ((syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_r, dv_C_k, fresh_k_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((Class.cv a)).fv ((Class.cv r)).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((Class.cv a)).fv ((Class.cv r)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (a), NFChoice.Compiler.CoreFVSimp.fv_class_cv (r)]; exact (show Disjoint (({a} : Finset Var)) (({r} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show a ∉ ({r} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ r from (by exact fresh_a_ne_r))))))))
  have dv_cache_0003 : Disjoint ((Class.cv a)).fv (X).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint ((Class.cv a)).fv (X).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({a} : Finset Var)) ((X).fv) from (Finset.disjoint_singleton_left.mpr (show a ∉ (X).fv from (by exact fresh_a_not_X))))))
  have dv_cache_0004 : k ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : Disjoint ((Class.cv r)).fv (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint ((Class.cv r)).fv (X).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({r} : Finset Var)) ((X).fv) from (Finset.disjoint_singleton_left.mpr (show r ∉ (X).fv from (by exact fresh_r_not_X))))))
  have dv_cache_0006 : k ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : k ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((syn_cfv (syn_c1st) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_cfv (syn_c1st) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((syn_cfv (syn_c2nd) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_cfv (syn_c2nd) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : r ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C)) (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X))) (.imp (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, fresh_r_not_X, fresh_r_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C)) (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X))) (.imp (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_C, fresh_a_not_X, fresh_a_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    @g_hwcnweclndv (syn_cpw X) C
  have p0001 :=
    @g_hwcnbaseclndv (syn_cpw X) C
  have p0002 :=
    @g_jca (.classMem C (syn_chwcn (syn_cpw X))) (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C)) (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X)) p0000 p0001
  have p0003 :=
    Nominal.mp hyp_cfbwpphwcncarrierinjndv_2 p0002
  have p0004 :=
    @g_fvex C (syn_c1st)
  have p0005 :=
    @g_fvex C (syn_c2nd)
  have p0006 :=
    @g_simpl (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))
  have p0007 :=
    @g_simpr (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))
  have p0008 :=
    @g_breq12d (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (.cv r) (syn_cfv (syn_c1st) C) (.cv a) (syn_cfv (syn_c2nd) C) (syn_cwe) p0006 p0007
  have p0009 :=
    @g_simpr (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))
  have p0010 :=
    @g_sseq1d (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (.cv a) (syn_cfv (syn_c2nd) C) (syn_cpw X) p0009
  have p0011 :=
    @g_anbi12d (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (syn_wbr (.cv r) (syn_cwe) (.cv a)) (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C)) (syn_wss (.cv a) (syn_cpw X)) (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X)) p0008 p0010
  have p0012 :=
    @g_simpr (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))
  have p0013 :=
    @g_pw1eq (.cv a) (syn_cfv (syn_c2nd) C)
  have p0014 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (.classEq (.cv a) (syn_cfv (syn_c2nd) C)) (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cfv (syn_c2nd) C))) p0012 p0013
  have p0015 :=
    @g_pw1eq (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cfv (syn_c2nd) C))
  have p0016 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cfv (syn_c2nd) C))) (.classEq (syn_cpw1 (syn_cpw1 (.cv a))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) p0014 p0015
  have p0017 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (.cv a))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))
  have p0018 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (.classEq (syn_cpw1 (syn_cpw1 (.cv a))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (.classEq (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))) p0016 p0017
  have p0019 :=
    @g_f1eq2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X))) (.cv k)
  have p0020 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (.classEq (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))) (syn_wb (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a)))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X))))) p0018 p0019
  have p0021 :=
    @g_exbidv (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a)))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X)))) k dv_cache_0001 p0020
  have p0022 :=
    @g_imbi2d (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_wwpp) p0021
  have p0023 :=
    @g_imbi12d (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) C)) (.classEq (.cv a) (syn_cfv (syn_c2nd) C))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv a)) (syn_wss (.cv a) (syn_cpw X))) (syn_wa (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C)) (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X))) (.imp (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (.imp (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X)))))) p0011 p0022
  have p0024 :=
    @g_vex r
  have p0025 :=
    @g_vex a
  have p0026 :=
    @g_cfbfdwppcarrierimpndv (.cv a) (.cv r) k X dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0024 p0025 hyp_cfbwpphwcncarrierinjndv_1 hyp_cfbwpphwcncarrierinjndv_3
  have p0027 :=
    @g_vtocl2 (.imp (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv a)) (syn_wss (.cv a) (syn_cpw X))) (.imp (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (.cv a)))) (syn_cpw (syn_cpw (syn_chnord X))))))) (.imp (syn_wa (syn_wbr (syn_cfv (syn_c1st) C) (syn_cwe) (syn_cfv (syn_c2nd) C)) (syn_wss (syn_cfv (syn_c2nd) C) (syn_cpw X))) (.imp (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X))))))) r a (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0004 p0005 p0023 p0026
  have p0028 :=
    Nominal.mp p0003 p0027
  exact p0028

noncomputable def g_cfbhnpw13genericraisedcodendv
    (C : Class) (X : Class) (hyp_cfbhnpw13genericraisedcodendv_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_cfbhnpw13genericraisedcodendv_2 : Nominal.NPrf (.classMem C (syn_chwcn (syn_cpw X)))) :
    Nominal.NPrf (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))))) := by
  let proofSupport : Finset Var := C.fv ∪ X.fv
  have p0000 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0001 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericraisedcodendv_2 p0000
  have p0002 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0003 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0002
  have p0004 :=
    Nominal.mp p0001 p0003
  have p0005 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0006 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) p0004 p0005
  have p0007 :=
    @g_hnsicodemapfndv (syn_cpw1 (syn_cpw X))
  have p0008 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) p0007
  have p0009 :=
    Nominal.mp p0006 p0008
  have p0010 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0011 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))) p0009 p0010
  have p0012 :=
    @g_hnsicodemapfndv (syn_cpw1 (syn_cpw1 (syn_cpw X)))
  have p0013 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0012
  have p0014 :=
    Nominal.mp p0011 p0013
  have p0015 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0016 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericraisedcodendv_2 p0015
  have p0017 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0018 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0017
  have p0019 :=
    Nominal.mp p0016 p0018
  have p0020 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0021 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) p0019 p0020
  have p0022 :=
    @g_hnsicodemapfndv (syn_cpw1 (syn_cpw X))
  have p0023 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) p0022
  have p0024 :=
    Nominal.mp p0021 p0023
  have p0025 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0026 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))) p0024 p0025
  have p0027 :=
    @g_hnsicodemapvalclndv (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
  have p0028 :=
    Nominal.mp p0026 p0027
  have p0029 :=
    @g_fveq2i (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))))) (syn_c2nd) p0028
  have p0030 :=
    @g_fvex (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_c1st)
  have p0031 :=
    @g_siex (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) p0030
  have p0032 :=
    @g_fvex (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_c2nd)
  have p0033 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) p0032
  have p0034 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))) p0031 p0033
  have p0035 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))) p0029 p0034
  have p0036 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0037 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericraisedcodendv_2 p0036
  have p0038 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0039 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0038
  have p0040 :=
    Nominal.mp p0037 p0039
  have p0041 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0042 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) p0040 p0041
  have p0043 :=
    @g_hnsicodemapfndv (syn_cpw1 (syn_cpw X))
  have p0044 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) p0043
  have p0045 :=
    Nominal.mp p0042 p0044
  have p0046 :=
    @g_elex (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_unisn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) p0047
  have p0049 :=
    @g_fveq2i (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_c2nd) p0048
  have p0050 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))
  have p0051 :=
    Nominal.mp p0049 p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) p0035 p0051
  have p0053 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0054 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericraisedcodendv_2 p0053
  have p0055 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0056 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0055
  have p0057 :=
    Nominal.mp p0054 p0056
  have p0058 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0059 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) p0057 p0058
  have p0060 :=
    @g_hnsicodemapvalclndv (syn_cpw1 (syn_cpw X)) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
  have p0061 :=
    Nominal.mp p0059 p0060
  have p0062 :=
    @g_fveq2i (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_c2nd) p0061
  have p0063 :=
    @g_fvex (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_c1st)
  have p0064 :=
    @g_siex (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) p0063
  have p0065 :=
    @g_fvex (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_c2nd)
  have p0066 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) p0065
  have p0067 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) p0064 p0066
  have p0068 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) p0062 p0067
  have p0069 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0070 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericraisedcodendv_2 p0069
  have p0071 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0072 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0071
  have p0073 :=
    Nominal.mp p0070 p0072
  have p0074 :=
    @g_elex (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_unisn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0075
  have p0077 :=
    @g_fveq2i (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_c2nd) p0076
  have p0078 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))
  have p0079 :=
    Nominal.mp p0077 p0078
  have p0080 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) p0068 p0079
  have p0081 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))
  have p0082 :=
    Nominal.mp p0080 p0081
  have p0083 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) p0052 p0082
  have p0084 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0085 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericraisedcodendv_2 p0084
  have p0086 :=
    @g_hnsicodemapvalclndv (syn_cpw X) (syn_csn C)
  have p0087 :=
    Nominal.mp p0085 p0086
  have p0088 :=
    @g_fveq2i (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn C)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C))))) (syn_c2nd) p0087
  have p0089 :=
    @g_fvex (syn_cuni (syn_csn C)) (syn_c1st)
  have p0090 :=
    @g_siex (syn_cfv (syn_c1st) (syn_cuni (syn_csn C))) p0089
  have p0091 :=
    @g_fvex (syn_cuni (syn_csn C)) (syn_c2nd)
  have p0092 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C))) p0091
  have p0093 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn C)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C)))) p0090 p0092
  have p0094 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn C)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C)))) p0088 p0093
  have p0095 :=
    @g_elex C (syn_chwcn (syn_cpw X))
  have p0096 :=
    Nominal.mp hyp_cfbhnpw13genericraisedcodendv_2 p0095
  have p0097 :=
    @g_unisn C p0096
  have p0098 :=
    @g_fveq2i (syn_cuni (syn_csn C)) C (syn_c2nd) p0097
  have p0099 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C))) (syn_cfv (syn_c2nd) C)
  have p0100 :=
    Nominal.mp p0098 p0099
  have p0101 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn C)))) (syn_cpw1 (syn_cfv (syn_c2nd) C)) p0094 p0100
  have p0102 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cpw1 (syn_cfv (syn_c2nd) C))
  have p0103 :=
    Nominal.mp p0101 p0102
  have p0104 :=
    @g_pw1eq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))
  have p0105 :=
    Nominal.mp p0103 p0104
  have p0106 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) p0083 p0105
  have p0107 :=
    @g_pm3_2i (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C))))) p0014 p0106
  exact p0107

#print axioms g_cfbhnpw13genericraisedcodendv

end NFChoice.DirectNominalPrf.WPPReplay
