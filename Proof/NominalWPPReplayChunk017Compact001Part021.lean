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
import NominalWPPReplayChunk017Compact001Part020

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

noncomputable def g_hncodecutreledgedecode
    (x : Var) (v : Var) (u : Var) (A : Class) (C : Class) (dv_A_C : Disjoint A.fv C.fv) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_C_u : u ∉ C.fv) (dv_C_v : v ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf (.imp (syn_wbr C (syn_chncodecutrel A) (.cv v)) (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ C.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_ne_v : p ≠ v := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_ne_p : v ≠ p :=
    Ne.symm fresh_p_ne_v
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_p : u ≠ p :=
    Ne.symm fresh_p_ne_u
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ ((syn_cop C (.cv v))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_C, fresh_p_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chncodecutinputs A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_chncodecutpairfn)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show p ≠ u from (by exact fresh_p_ne_u))
  have dv_cache_0008 : p ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0009 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0010 : x ∉ ((syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, dv_A_x, dv_C_x, (Ne.symm dv_v_x), (Ne.symm dv_u_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_p, dv_A_u, dv_C_u, dv_u_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_u, fresh_p_not_C, fresh_p_ne_x, fresh_p_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr C (syn_chncodecutrel A) (.cv v))))
  have p0001 :=
    @g_biimpi (syn_wbr C (syn_chncodecutrel A) (.cv v)) (.classMem (syn_cop C (.cv v)) (syn_chncodecutrel A)) p0000
  have p0002 :=
    (by simpa [syn_chncodecutrel] using (Nominal.classEqRefl (syn_chncodecutrel A)))
  have p0003 :=
    @g_eleq2i (syn_chncodecutrel A) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) (syn_cop C (.cv v)) p0002
  have p0004 :=
    @g_sylib (syn_wbr C (syn_chncodecutrel A) (.cv v)) (.classMem (syn_cop C (.cv v)) (syn_chncodecutrel A)) (.classMem (syn_cop C (.cv v)) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A))) p0001 p0003
  have p0005 :=
    @g_hncodecutpairfnfn
  have p0006 :=
    @g_fnfun (syn_cvv) (syn_chncodecutpairfn)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_fvelima p (syn_cop C (.cv v)) (syn_chncodecutinputs A) (syn_chncodecutpairfn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_mpan (syn_wfun (syn_chncodecutpairfn)) (.classMem (syn_cop C (.cv v)) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A))) (syn_wrex p (syn_chncodecutinputs A) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) p0007 p0008
  have p0010 :=
    @g_syl (syn_wbr C (syn_chncodecutrel A) (.cv v)) (.classMem (syn_cop C (.cv v)) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A))) (syn_wrex p (syn_chncodecutinputs A) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) p0004 p0009
  have p0011 :=
    @g_simpl (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))
  have p0012 :=
    @g_hncodecutinputdecode x u A p dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv p) (syn_chncodecutinputs A)) (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))) p0011 p0012
  have p0014 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
  have p0015 :=
    @g_fveq2d (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))) (syn_chncodecutpairfn) p0014
  have p0016 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
  have p0017 :=
    @g_simpr (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0016 p0017
  have p0019 :=
    @g_hncodecutpairfnvalhwcn x u A dv_cache_0005
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u))) p0018 p0019
  have p0021 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)) p0015 p0020
  have p0022 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)) p0021
  have p0023 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
  have p0024 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))
  have p0025 :=
    @g_simpr (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))) p0024 p0025
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))) p0023 p0026
  have p0028 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)) (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)) p0022 p0027
  have p0029 :=
    @g_opth (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u) C (.cv v)
  have p0030 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (.classEq (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)) (syn_cop C (.cv v))) (syn_wa (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C) (.classEq (.cv u) (.cv v))) p0028 p0029
  have p0031 :=
    @g_simpl (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C) (.classEq (.cv u) (.cv v))
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_wa (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C) (.classEq (.cv u) (.cv v))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C) p0030 p0031
  have p0033 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C p0032
  have p0034 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
  have p0035 :=
    @g_fveq2d (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))) (syn_chncodecutpairfn) p0034
  have p0036 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
  have p0037 :=
    @g_simpr (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0036 p0037
  have p0039 :=
    @g_hncodecutpairfnvalhwcn x u A dv_cache_0005
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u))) p0038 p0039
  have p0041 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)) p0035 p0040
  have p0042 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)) p0041
  have p0043 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
  have p0044 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))
  have p0045 :=
    @g_simpr (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))
  have p0046 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))) p0044 p0045
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))) p0043 p0046
  have p0048 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)) (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)) p0042 p0047
  have p0049 :=
    @g_opth (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u) C (.cv v)
  have p0050 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (.classEq (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)) (syn_cop C (.cv v))) (syn_wa (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C) (.classEq (.cv u) (.cv v))) p0048 p0049
  have p0051 :=
    @g_simpr (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C) (.classEq (.cv u) (.cv v))
  have p0052 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_wa (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C) (.classEq (.cv u) (.cv v))) (.classEq (.cv u) (.cv v)) p0050 p0051
  have p0053 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (.cv u) (.cv v) p0052
  have p0054 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u)) p0033 p0053
  have p0055 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u))) p0054
  have p0056 :=
    @g_reximdv (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u))) x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0010 p0055
  have p0057 :=
    @g_reximdva (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u)))) u (syn_chwcn A) dv_cache_0011 p0056
  have p0058 :=
    @g_mpd (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))) (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u))))) p0013 p0057
  have p0059 :=
    @g_ex (.classMem (.cv p) (syn_chncodecutinputs A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))) (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u))))) p0058
  have p0060 :=
    @g_rexlimiv (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))) (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u))))) p (syn_chncodecutinputs A) dv_cache_0012 p0059
  have p0061 :=
    @g_syl (syn_wbr C (syn_chncodecutrel A) (.cv v)) (syn_wrex p (syn_chncodecutinputs A) (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))) (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (.cv v) (.cv u))))) p0010 p0060
  exact p0061

noncomputable def g_hncodecutfnvalhwcn
    (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_hwcnpair u A
  have p0001 :=
    @g_opeq1d (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv x)) p0000
  have p0002 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn A)) (syn_cop (.cv u) (syn_csn (.cv x))) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv x))) (syn_chncodecutfn) p0001
  have p0003 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0004 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0005 :=
    @g_hncodecutfnval x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) p0003 p0004
  have p0006 :=
    @g_a1i (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv x)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classMem (.cv u) (syn_chwcn A)) p0005
  have p0007 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv x)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) p0002 p0006
  exact p0007

noncomputable def g_hncodecutreledgedecodetarget
    (x : Var) (v : Var) (A : Class) (C : Class) (dv_A_C : Disjoint A.fv C.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_C_v : v ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_v_x : v ≠ x) :
    Nominal.NPrf (.imp (syn_wbr C (syn_chncodecutrel A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ A.fv ∪ C.fv
  let z : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have dv_cache_0001 : Disjoint (A).fv (C).fv := by
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0009 : u ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0010 : v ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0011 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv v))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint (({x} : Finset Var)) ((((Class.cv v)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({x} : Finset Var)) (((Class.cv v)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) (({v} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({v} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ v from (by exact Ne.symm dv_v_x)))))))), (show Disjoint (({x} : Finset Var)) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint (({x} : Finset Var)) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0012 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_v_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((Wff.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, fresh_x_ne_z, (Ne.symm dv_v_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_v, fresh_z_not_C, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : u ∉ ((syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_v, fresh_u_not_C, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hncodecutreledgedecode z v u A C dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))
  have p0002 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
  have p0003 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))) p0001 p0002
  have p0004 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))
  have p0005 :=
    @g_simpr (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))
  have p0006 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))) (.classEq (.cv v) (.cv u)) p0004 p0005
  have p0007 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (.cv v) (.cv u) p0006
  have p0008 :=
    @g_fveq2d (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (.cv u) (.cv v) (syn_c2nd) p0007
  have p0009 :=
    @g_eleqtrd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (.cv z) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) p0003 p0008
  have p0010 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))
  have p0011 :=
    @g_simpl (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))
  have p0012 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) p0010 p0011
  have p0013 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))
  have p0014 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
  have p0015 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) p0013 p0014
  have p0016 :=
    @g_hncodecutfnvalhwcn z u A dv_cache_0002
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv z)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) p0015 p0016
  have p0018 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv z)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)) p0017
  have p0019 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))
  have p0020 :=
    @g_simpr (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))) (.classEq (.cv v) (.cv u)) p0019 p0020
  have p0022 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (.cv v) (.cv u) p0021
  have p0023 :=
    @g_opeq1d (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (.cv u) (.cv v) (syn_csn (.cv z)) p0022
  have p0024 :=
    @g_fveq2d (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cop (.cv v) (syn_csn (.cv z))) (syn_chncodecutfn) p0023
  have p0025 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))
  have p0026 :=
    @g_simpr (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))
  have p0027 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))) (.classEq (.cv v) (.cv u)) p0025 p0026
  have p0028 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))
  have p0029 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
  have p0030 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) p0028 p0029
  have p0031 :=
    @g_eqeltrd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (.cv v) (.cv u) (syn_chwcn A) p0027 p0030
  have p0032 :=
    @g_hncodecutfnvalhwcn z v A dv_cache_0003
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv z)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))) p0031 p0032
  have p0034 :=
    @g_n_3eqtrd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)) (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv z)))) (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv z)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)) p0018 p0024 p0033
  have p0035 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)) p0012 p0034
  have p0036 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))) p0009 p0035
  have p0037 :=
    @g_hnwcutcodeeq3 (.cv x) (.cv z) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v)) dv_cache_0011
  have p0038 :=
    @g_eqeq2d (.classEq (.cv x) (.cv z)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)) C p0037
  have p0039 :=
    @g_rspcev (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))) x (.cv z) (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0012 dv_cache_0013 dv_cache_0014 p0038
  have p0040 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0036 p0039
  have p0041 :=
    @g_ex (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0040
  have p0042 :=
    @g_rexlimdva (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) z (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0015 dv_cache_0016 p0041
  have p0043 :=
    @g_rexlimiv (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) u (syn_chwcn A) dv_cache_0017 p0042
  have p0044 :=
    @g_syl (syn_wbr C (syn_chncodecutrel A) (.cv v)) (syn_wrex u (syn_chwcn A) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) (.classEq (.cv v) (.cv u))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0000 p0043
  exact p0044

noncomputable def g_hncodecutreledgeihwcn
    (x : Var) (v : Var) (A : Class) (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chncodecutrel A) (.cv v))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ A.fv
  have dv_cache_0001 : Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv v))).fv := by
    exact (show Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv v))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint ((A).fv) ((((Class.cv v)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv v)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({v} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show v ∉ (A).fv from (by exact dv_A_v)))))), (show Disjoint ((A).fv) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have p0000 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
  have p0001 :=
    @g_hwcnpair v A
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))) p0000 p0001
  have p0003 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
  have p0004 :=
    @g_eqeltrrd (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) (syn_chwcn A) p0002 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
  have p0006 :=
    @g_jca (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0004 p0005
  have p0007 :=
    @g_fvex (.cv v) (syn_c1st)
  have p0008 :=
    @g_fvex (.cv v) (syn_c2nd)
  have p0009 :=
    @g_hncodecutreledgei x A (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v)) dv_cache_0001 p0007 p0008
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chncodecutrel A) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))) p0006 p0009
  have p0011 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
  have p0012 :=
    @g_hwcnpair v A
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))) p0011 p0012
  have p0014 :=
    @g_eqcomd (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) p0013
  have p0015 :=
    @g_breq2d (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) (.cv v) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chncodecutrel A) p0014
  have p0016 :=
    @g_mpbid (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chncodecutrel A) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chncodecutrel A) (.cv v)) p0010 p0015
  exact p0016

#print axioms g_hncodecutreledgeihwcn

end NFChoice.DirectNominalPrf.WPPReplay
