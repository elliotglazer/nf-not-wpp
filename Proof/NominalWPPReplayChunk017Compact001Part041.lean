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
import NominalWPPReplayChunk017Compact001Part040

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

noncomputable def g_hncodepredendsmemndv
    (x : Var) (v : Var) (u : Var) (A : Class) (X : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_X_u : u ∉ X.fv) (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) :
    Nominal.NPrf (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ X.fv
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
  have fresh_p_not_X : p ∉ X.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ ((syn_chncodepredinputs A X v)).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredinputs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_X, fresh_p_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_c2nd)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0008 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0009 : p ∉ ((syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_v, fresh_p_not_X, fresh_p_ne_u, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((Wff.classMem (.cv v) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_v, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_cop (.cv v) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_v, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((Wff.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chncodepredends] using (Nominal.classEqRefl (syn_chncodepredends A X v)))
  have p0001 :=
    @g_eleq2i (syn_chncodepredends A X v) (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))) (.cv x) p0000
  have p0002 :=
    @g_ln2ndfn
  have p0003 :=
    @g_fnfun (syn_cvv) (syn_c2nd)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_eluniima p (syn_chncodepredinputs A X v) (.cv x) (syn_c2nd) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_bitri (.classMem (.cv x) (syn_chncodepredends A X v)) (.classMem (.cv x) (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v)))) (syn_wrex p (syn_chncodepredinputs A X v) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) p0001 p0006
  have p0008 :=
    @g_a1i (syn_wb (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wrex p (syn_chncodepredinputs A X v) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))) (.classMem (.cv v) (syn_chwcn A)) p0007
  have p0009 :=
    @g_biimpd (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wrex p (syn_chncodepredinputs A X v) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) p0008
  have p0010 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
  have p0011 :=
    @g_simpld (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))) (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))) p0010
  have p0012 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
  have p0013 :=
    @g_simpl (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0014 :=
    @g_hncodepredinputsssndv v A X dv_cache_0004
  have p0015 :=
    @g_sseli (syn_chncodepredinputs A X v) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0014
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0013 p0015
  have p0017 :=
    @g_n_1st2nd2 (.cv p) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classEq (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)))) p0016 p0017
  have p0019 :=
    @g_simpl (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0020 :=
    @g_hncodepredinputsssndv v A X dv_cache_0004
  have p0021 :=
    @g_sseli (syn_chncodepredinputs A X v) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0020
  have p0022 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0019 p0021
  have p0023 :=
    @g_simpl (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0024 :=
    @g_hncodepredinputsssndv v A X dv_cache_0004
  have p0025 :=
    @g_sseli (syn_chncodepredinputs A X v) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0024
  have p0026 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0023 p0025
  have p0027 :=
    @g_n_1st2nd2 (.cv p) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0028 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classEq (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)))) p0026 p0027
  have p0029 :=
    @g_eleq1d (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0028
  have p0030 :=
    @g_mpbid (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0022 p0029
  have p0031 :=
    @g_opelxp (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0032 :=
    @g_a1i (syn_wb (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) p0031
  have p0033 :=
    @g_mpbid (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0030 p0032
  have p0034 :=
    @g_simpld (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0033
  have p0035 :=
    @g_elsni (syn_cfv (syn_c1st) (.cv p)) (.cv v)
  have p0036 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_c1st) (.cv p)) (.cv v)) p0034 p0035
  have p0037 :=
    @g_simpl (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0038 :=
    @g_hncodepredinputsssndv v A X dv_cache_0004
  have p0039 :=
    @g_sseli (syn_chncodepredinputs A X v) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0038
  have p0040 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0037 p0039
  have p0041 :=
    @g_simpl (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0042 :=
    @g_hncodepredinputsssndv v A X dv_cache_0004
  have p0043 :=
    @g_sseli (syn_chncodepredinputs A X v) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0042
  have p0044 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0041 p0043
  have p0045 :=
    @g_n_1st2nd2 (.cv p) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0046 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classEq (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)))) p0044 p0045
  have p0047 :=
    @g_eleq1d (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0046
  have p0048 :=
    @g_mpbid (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0040 p0047
  have p0049 :=
    @g_opelxp (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0050 :=
    @g_a1i (syn_wb (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) p0049
  have p0051 :=
    @g_mpbid (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0048 p0050
  have p0052 :=
    @g_simprd (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0051
  have p0053 :=
    @g_pw1argclcl (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv p))
  have p0054 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) (syn_cfv (syn_c2nd) (.cv v))) (.classEq (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))))) p0052 p0053
  have p0055 :=
    @g_simprd (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) (syn_cfv (syn_c2nd) (.cv v))) (.classEq (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p))))) p0054
  have p0056 :=
    @g_simpr (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0057 :=
    @g_simpl (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0058 :=
    @g_hncodepredinputsssndv v A X dv_cache_0004
  have p0059 :=
    @g_sseli (syn_chncodepredinputs A X v) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0058
  have p0060 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0057 p0059
  have p0061 :=
    @g_simpl (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))
  have p0062 :=
    @g_hncodepredinputsssndv v A X dv_cache_0004
  have p0063 :=
    @g_sseli (syn_chncodepredinputs A X v) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0062
  have p0064 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0061 p0063
  have p0065 :=
    @g_n_1st2nd2 (.cv p) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0066 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classEq (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)))) p0064 p0065
  have p0067 :=
    @g_eleq1d (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0066
  have p0068 :=
    @g_mpbid (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0060 p0067
  have p0069 :=
    @g_opelxp (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0070 :=
    @g_a1i (syn_wb (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) p0069
  have p0071 :=
    @g_mpbid (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0068 p0070
  have p0072 :=
    @g_simprd (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cfv (syn_c1st) (.cv p)) (syn_csn (.cv v))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0071
  have p0073 :=
    @g_pw1argclcl (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv p))
  have p0074 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cfv (syn_c2nd) (.cv p)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) (syn_cfv (syn_c2nd) (.cv v))) (.classEq (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))))) p0072 p0073
  have p0075 :=
    @g_simprd (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) (syn_cfv (syn_c2nd) (.cv v))) (.classEq (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p))))) p0074
  have p0076 :=
    @g_eleqtrd (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.cv x) (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))) p0056 p0075
  have p0077 :=
    @g_elsni (.cv x) (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))
  have p0078 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv x) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p))))) (.classEq (.cv x) (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))) p0076 p0077
  have p0079 :=
    @g_eqcomd (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.cv x) (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) p0078
  have p0080 :=
    @g_sneqd (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv p))) (.cv x) p0079
  have p0081 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv p)))) (syn_csn (.cv x)) p0055 p0080
  have p0082 :=
    @g_opeq12d (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (syn_cfv (syn_c1st) (.cv p)) (.cv v) (syn_cfv (syn_c2nd) (.cv p)) (syn_csn (.cv x)) p0036 p0081
  have p0083 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.cv p) (syn_cop (syn_cfv (syn_c1st) (.cv p)) (syn_cfv (syn_c2nd) (.cv p))) (syn_cop (.cv v) (syn_csn (.cv x))) p0018 p0082
  have p0084 :=
    @g_syl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classEq (.cv p) (syn_cop (.cv v) (syn_csn (.cv x)))) p0012 p0083
  have p0085 :=
    @g_eleq1d (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))) (.cv p) (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v) p0084
  have p0086 :=
    @g_mpbid (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))) (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) p0011 p0085
  have p0087 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))
  have p0088 :=
    @g_hncodepredinputmemndv x v u A X dv_cache_0005 dv_cache_0004 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0089 :=
    @g_syl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))) (.classMem (.cv v) (syn_chwcn A)) (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0087 p0088
  have p0090 :=
    @g_mpbid (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))))) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0086 p0089
  have p0091 :=
    @g_rexlimdvaa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p (syn_chncodepredinputs A X v) dv_cache_0009 dv_cache_0010 p0090
  have p0092 :=
    @g_syld (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wrex p (syn_chncodepredinputs A X v) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0009 p0091
  have p0093 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
  have p0094 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
  have p0095 :=
    @g_hncodepredinputmemndv x v u A X dv_cache_0005 dv_cache_0004 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0096 :=
    @g_biimprd (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0095
  have p0097 :=
    @g_syl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (.classMem (.cv v) (syn_chwcn A)) (.imp (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v))) p0094 p0096
  have p0098 :=
    @g_mpd (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) p0093 p0097
  have p0099 :=
    @g_vex x
  have p0100 :=
    @g_snid (.cv x) p0099
  have p0101 :=
    @g_vex v
  have p0102 :=
    @g_snex (.cv x)
  have p0103 :=
    @g_opfv2nd (.cv v) (syn_csn (.cv x)) p0101 p0102
  have p0104 :=
    @g_eleqtrri (.cv x) (syn_csn (.cv x)) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x)))) p0100 p0103
  have p0105 :=
    @g_a1i (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0104
  have p0106 :=
    @g_jca (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x))))) p0098 p0105
  have p0107 :=
    @g_id (.classEq (.cv p) (syn_cop (.cv v) (syn_csn (.cv x))))
  have p0108 :=
    @g_fveq2d (.classEq (.cv p) (syn_cop (.cv v) (syn_csn (.cv x)))) (.cv p) (syn_cop (.cv v) (syn_csn (.cv x))) (syn_c2nd) p0107
  have p0109 :=
    @g_eleq2d (.classEq (.cv p) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (.cv p)) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x)))) (.cv x) p0108
  have p0110 :=
    @g_rspcev (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x))))) p (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v) dv_cache_0011 dv_cache_0001 dv_cache_0012 p0109
  have p0111 :=
    @g_syl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (syn_wa (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cop (.cv v) (syn_csn (.cv x)))))) (syn_wrex p (syn_chncodepredinputs A X v) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) p0106 p0110
  have p0112 :=
    (by simpa [syn_chncodepredends] using (Nominal.classEqRefl (syn_chncodepredends A X v)))
  have p0113 :=
    @g_eleq2i (syn_chncodepredends A X v) (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))) (.cv x) p0112
  have p0114 :=
    @g_ln2ndfn
  have p0115 :=
    @g_fnfun (syn_cvv) (syn_c2nd)
  have p0116 :=
    Nominal.mp p0114 p0115
  have p0117 :=
    @g_eluniima p (syn_chncodepredinputs A X v) (.cv x) (syn_c2nd) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0118 :=
    Nominal.mp p0116 p0117
  have p0119 :=
    @g_bitri (.classMem (.cv x) (syn_chncodepredends A X v)) (.classMem (.cv x) (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v)))) (syn_wrex p (syn_chncodepredinputs A X v) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) p0113 p0118
  have p0120 :=
    @g_biimpri (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wrex p (syn_chncodepredinputs A X v) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) p0119
  have p0121 :=
    @g_syl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (syn_wrex p (syn_chncodepredinputs A X v) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv p)))) (.classMem (.cv x) (syn_chncodepredends A X v)) p0111 p0120
  have p0122 :=
    @g_ex (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv x) (syn_chncodepredends A X v)) p0121
  have p0123 :=
    @g_impbid (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0092 p0122
  exact p0123

noncomputable def g_hncodepredendsssndv
    (v : Var) (A : Class) (X : Class) (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wss (syn_chncodepredends A X v) (syn_cfv (syn_c2nd) (.cv v)))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ A.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_X : u ∉ X.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0005 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0006 : x ∉ ((syn_chncodepredends A X v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_X, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (.cv v) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hncodepredendsmemndv x v u A X dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_biimpd (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0000
  have p0002 :=
    @g_simpl (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0003 :=
    @g_syl6 (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0001 p0002
  have p0004 :=
    @g_ssrdv (.classMem (.cv v) (syn_chwcn A)) x (syn_chncodepredends A X v) (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0003
  exact p0004

#print axioms g_hncodepredendsssndv

end NFChoice.DirectNominalPrf.WPPReplay
