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
import NominalWPPReplayChunk012BCompact001Part025

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

noncomputable def g_otsnelsi3
    (A : Class) (B : Class) (C : Class) (R : Class) (hyp_otsnelsi3_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_otsnelsi3_2 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_otsnelsi3_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))) (syn_csi3 R)) (.classMem (syn_cop A (syn_cop B C)) R)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_p_ne_x : p ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have dv_cache_0001 : p ∉ ((syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, fresh_p_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_c2nd)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cproj2 (.cv p))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_cop A (syn_cop B C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, fresh_p_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_csi3] using (Nominal.classEqRefl (syn_csi3 R)))
  have p0001 :=
    @g_eleq2i (syn_csi3 R) (syn_cima (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_cpw1 R)) (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))) p0000
  have p0002 :=
    @g_elimapw1 p (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))) (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) R dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @g_oteltxp (syn_csn (.cv p)) (syn_csn A) (syn_cop (syn_csn B) (syn_csn C)) (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))
  have p0004 :=
    @g_vex p
  have p0005 :=
    @g_opsnelsi (.cv p) A (syn_c1st) p0004 hyp_otsnelsi3_1
  have p0006 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c1st) A)))
  have p0007 :=
    @g_bitr4i (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn A)) (syn_csi (syn_c1st))) (.classMem (syn_cop (.cv p) A) (syn_c1st)) (syn_wbr (.cv p) (syn_c1st) A) p0005 p0006
  have p0008 :=
    @g_oteltxp (syn_csn (.cv p)) (syn_csn B) (syn_csn C) (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))
  have p0009 :=
    @g_opsnelsi (.cv p) B (syn_ccom (syn_c1st) (syn_c2nd)) p0004 hyp_otsnelsi3_2
  have p0010 :=
    @g_opelco x (.cv p) B (syn_c1st) (syn_c2nd) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0011 :=
    @g_opeq (.cv p)
  have p0012 :=
    @g_breq1i (.cv p) (syn_cop (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p))) (.cv x) (syn_c2nd) p0011
  have p0013 :=
    @g_proj1ex (.cv p) p0004
  have p0014 :=
    @g_proj2ex (.cv p) p0004
  have p0015 :=
    @g_opbr2nd (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p)) (.cv x) p0013 p0014
  have p0016 :=
    @g_eqcom (syn_cproj2 (.cv p)) (.cv x)
  have p0017 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (syn_cop (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p))) (syn_c2nd) (.cv x)) (.classEq (syn_cproj2 (.cv p)) (.cv x)) (.classEq (.cv x) (syn_cproj2 (.cv p))) p0012 p0015 p0016
  have p0018 :=
    @g_anbi1i (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c1st) B) p0017
  have p0019 :=
    @g_exbii (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c1st) B)) (syn_wa (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c1st) B)) x p0018
  have p0020 :=
    @g_breq1 (.cv x) (syn_cproj2 (.cv p)) B (syn_c1st)
  have p0021 :=
    @g_ceqsexv (syn_wbr (.cv x) (syn_c1st) B) (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B) x (syn_cproj2 (.cv p)) dv_cache_0008 dv_cache_0009 p0014 p0020
  have p0022 :=
    @g_bitri (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c1st) B))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c1st) B))) (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B) p0019 p0021
  have p0023 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn B)) (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))) (.classMem (syn_cop (.cv p) B) (syn_ccom (syn_c1st) (syn_c2nd))) (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c1st) B))) (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B) p0009 p0010 p0022
  have p0024 :=
    @g_opsnelsi (.cv p) C (syn_ccom (syn_c2nd) (syn_c2nd)) p0004 hyp_otsnelsi3_3
  have p0025 :=
    @g_opelco x (.cv p) C (syn_c2nd) (syn_c2nd) dv_cache_0004 dv_cache_0010 dv_cache_0007 dv_cache_0007
  have p0026 :=
    @g_anbi1i (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c2nd) C) p0017
  have p0027 :=
    @g_exbii (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c2nd) C)) (syn_wa (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c2nd) C)) x p0026
  have p0028 :=
    @g_breq1 (.cv x) (syn_cproj2 (.cv p)) C (syn_c2nd)
  have p0029 :=
    @g_ceqsexv (syn_wbr (.cv x) (syn_c2nd) C) (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C) x (syn_cproj2 (.cv p)) dv_cache_0008 dv_cache_0011 p0014 p0028
  have p0030 :=
    @g_bitri (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c2nd) C))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c2nd) C))) (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C) p0027 p0029
  have p0031 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn C)) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))) (.classMem (syn_cop (.cv p) C) (syn_ccom (syn_c2nd) (syn_c2nd))) (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c2nd) C))) (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C) p0024 p0025 p0030
  have p0032 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn B)) (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))) (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B) (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn C)) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))) (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C) p0023 p0031
  have p0033 :=
    @g_opbr2nd (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p)) (syn_cop B C) p0013 p0014
  have p0034 :=
    @g_breq1i (.cv p) (syn_cop (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p))) (syn_cop B C) (syn_c2nd) p0011
  have p0035 :=
    @g_op1st2nd B C (syn_cproj2 (.cv p)) hyp_otsnelsi3_2 hyp_otsnelsi3_3
  have p0036 :=
    @g_n_3bitr4ri (syn_wbr (syn_cop (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p))) (syn_c2nd) (syn_cop B C)) (.classEq (syn_cproj2 (.cv p)) (syn_cop B C)) (syn_wbr (.cv p) (syn_c2nd) (syn_cop B C)) (syn_wa (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B) (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C)) p0033 p0034 p0035
  have p0037 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn B) (syn_csn C))) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn B)) (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn C)) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_wa (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B) (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C)) (syn_wbr (.cv p) (syn_c2nd) (syn_cop B C)) p0008 p0032 p0036
  have p0038 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn A)) (syn_csi (syn_c1st))) (syn_wbr (.cv p) (syn_c1st) A) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn B) (syn_csn C))) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_wbr (.cv p) (syn_c2nd) (syn_cop B C)) p0007 p0037
  have p0039 :=
    @g_opex B C hyp_otsnelsi3_2 hyp_otsnelsi3_3
  have p0040 :=
    @g_op1st2nd A (syn_cop B C) (.cv p) hyp_otsnelsi3_1 p0039
  have p0041 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C)))) (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn A)) (syn_csi (syn_c1st))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn B) (syn_csn C))) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))) (syn_wa (syn_wbr (.cv p) (syn_c1st) A) (syn_wbr (.cv p) (syn_c2nd) (syn_cop B C))) (.classEq (.cv p) (syn_cop A (syn_cop B C))) p0003 p0038 p0040
  have p0042 :=
    @g_rexbii (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C)))) (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))) (.classEq (.cv p) (syn_cop A (syn_cop B C))) p R p0041
  have p0043 :=
    @g_risset p (syn_cop A (syn_cop B C)) R dv_cache_0012 dv_cache_0003
  have p0044 :=
    @g_bitr4i (syn_wrex p R (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C)))) (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))))) (syn_wrex p R (.classEq (.cv p) (syn_cop A (syn_cop B C)))) (.classMem (syn_cop A (syn_cop B C)) R) p0042 p0043
  have p0045 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))) (syn_csi3 R)) (.classMem (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))) (syn_cima (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_cpw1 R))) (syn_wrex p R (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C)))) (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))))) (.classMem (syn_cop A (syn_cop B C)) R) p0001 p0002 p0044
  exact p0045

noncomputable def g_si3ex
    (A : Class) (hyp_si3ex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_csi3 A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_csi3] using (Nominal.classEqRefl (syn_csi3 A)))
  have p0001 :=
    @g_n_1stex
  have p0002 :=
    @g_siex (syn_c1st) p0001
  have p0003 :=
    @g_n_1stex
  have p0004 :=
    @g_n_2ndex
  have p0005 :=
    @g_coex (syn_c1st) (syn_c2nd) p0003 p0004
  have p0006 :=
    @g_siex (syn_ccom (syn_c1st) (syn_c2nd)) p0005
  have p0007 :=
    @g_n_2ndex
  have p0008 :=
    @g_n_2ndex
  have p0009 :=
    @g_coex (syn_c2nd) (syn_c2nd) p0007 p0008
  have p0010 :=
    @g_siex (syn_ccom (syn_c2nd) (syn_c2nd)) p0009
  have p0011 :=
    @g_txpex (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))) p0006 p0010
  have p0012 :=
    @g_txpex (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))) p0002 p0011
  have p0013 :=
    @g_pw1ex A hyp_si3ex_1
  have p0014 :=
    @g_imaex (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_cpw1 A) p0012 p0013
  have p0015 :=
    @g_eqeltri (syn_csi3 A) (syn_cima (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))) (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_cpw1 A)) (syn_cvv) p0000 p0014
  exact p0015

noncomputable def g_releqel
    (x : Var) (y : Var) (A : Class) (R : Class) (T : Class) (dv_A_y : y ∉ A.fv) (dv_R_y : y ∉ R.fv) (dv_T_y : y ∉ T.fv) (dv_x_y : x ≠ y) (hyp_releqel_1 : Nominal.NPrf (.classMem T (syn_cvv))) (hyp_releqel_2 : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) T) R) (.classMem (.cv y) A))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) T) (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))) (.classEq (.cv x) A)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ R.fv ∪ T.fv
  have dv_cache_0001 : y ∉ ((syn_cop (.cv x) T)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_T_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elima1c y (syn_cop (.cv x) T) (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elsymdif (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins3 (syn_csset)) (syn_cins2 R)
  have p0002 :=
    @g_otelins3 (syn_csn (.cv y)) (.cv x) T (syn_csset) hyp_releqel_1
  have p0003 :=
    @g_vex y
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_opelssetsn (.cv y) (.cv x) p0003 p0004
  have p0006_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0006 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins3 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x) p0002 p0006_e01_recanon
  have p0007 :=
    @g_otelins2 (syn_csn (.cv y)) (.cv x) T R p0004
  have p0008 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins2 R)) (.classMem (syn_cop (syn_csn (.cv y)) T) R) (.classMem (.cv y) A) p0007 hyp_releqel_2
  have p0009 :=
    @g_bibi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins3 (syn_csset))) (.objMem y x) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins2 R)) (.classMem (.cv y) A) p0006 p0008
  have p0010 :=
    @g_xchbinx (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R))) (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins3 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins2 R))) (syn_wb (.objMem y x) (.classMem (.cv y) A)) p0001 p0009
  have p0011 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R))) (.neg (syn_wb (.objMem y x) (.classMem (.cv y) A))) y p0010
  have p0012 :=
    @g_exnal (syn_wb (.objMem y x) (.classMem (.cv y) A)) y
  have p0013 :=
    @g_n_3bitrri (.classMem (syn_cop (.cv x) T) (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))) (syn_wex y (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)))) (syn_wex y (.neg (syn_wb (.objMem y x) (.classMem (.cv y) A)))) (.neg (.all y (syn_wb (.objMem y x) (.classMem (.cv y) A)))) p0000 p0011 p0012
  have p0014 :=
    @g_con1bii (.all y (syn_wb (.objMem y x) (.classMem (.cv y) A))) (.classMem (syn_cop (.cv x) T) (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))) p0013
  have p0015 :=
    @g_opex (.cv x) T p0004 hyp_releqel_1
  have p0016 :=
    @g_elcompl (syn_cop (.cv x) T) (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)) p0015
  have p0017 :=
    @g_dfcleq y (.cv x) A dv_cache_0003 dv_cache_0004
  have p0018_e02_recanon : Nominal.NPrf (syn_wb (.classEq (.cv x) A) (.all y (syn_wb (.objMem y x) (.classMem (.cv y) A)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0017
  have p0018 :=
    @g_n_3bitr4i (.neg (.classMem (syn_cop (.cv x) T) (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))) (.all y (syn_wb (.objMem y x) (.classMem (.cv y) A))) (.classMem (syn_cop (.cv x) T) (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))) (.classEq (.cv x) A) p0014 p0016 p0018_e02_recanon
  exact p0018

noncomputable def g_releqmpt
    (x : Var) (y : Var) (A : Class) (R : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_V_y : y ∉ V.fv) (dv_x_y : x ≠ y) (hyp_releqmpt_1 : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) R) (.classMem (.cv y) V))) :
    Nominal.NPrf (.classEq (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))) (syn_cmpt x A V)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ R.fv ∪ V.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (V).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_V_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0005 : x ∉ ((syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (V).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_V, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elin (syn_cop (.cv x) (.cv z)) (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))
  have p0001 :=
    @g_vex z
  have p0002 :=
    @g_opelxp (.cv x) (.cv z) A (syn_cvv)
  have p0003 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv x) (.cv z)) (syn_cxp A (syn_cvv))) (.classMem (.cv x) A) (.classMem (.cv z) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_opelcnv (.cv x) (.cv z) (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_releqel z y V R (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0005 hyp_releqmpt_1
  have p0007 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv z)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))) (.classMem (syn_cop (.cv z) (.cv x)) (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))) (.classEq (.cv z) V) p0004 p0006
  have p0008 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv z)) (syn_cxp A (syn_cvv))) (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv z)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))) (.classEq (.cv z) V) p0003 p0007
  have p0009 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv z)) (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))) (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (syn_cxp A (syn_cvv))) (.classMem (syn_cop (.cv x) (.cv z)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) V)) p0000 p0008
  have p0010 :=
    @g_opabbi2i (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) V)) x z (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x z A V dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0012 :=
    @g_eqtr4i (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))) (syn_copab x z (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) V))) (syn_cmpt x A V) p0010 p0011
  exact p0012

noncomputable def g_releqmpt2
    (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (R : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_V_z : z ∉ V.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_releqmpt2_1 : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) R) (.classMem (.cv z) V))) :
    Nominal.NPrf (.classEq (syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))) (syn_cmpt2 x A y B V)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ V.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((Class.cv w)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (V).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_V_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_z), (Ne.symm dv_y_z), fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : w ∉ ((syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_not_B, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0009 : x ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0010 : y ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0011 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ (V).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_V, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eldif (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cxp (syn_cxp A B) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))
  have p0001 :=
    @g_vex w
  have p0002 :=
    @g_opelxp (syn_cop (.cv x) (.cv y)) (.cv w) (syn_cxp A B) (syn_cvv)
  have p0003 :=
    @g_mpbiran2 (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cxp (syn_cxp A B) (syn_cvv))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)) (.classMem (.cv w) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_opelxp (.cv x) (.cv y) A B
  have p0005 :=
    @g_bitri (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cxp (syn_cxp A B) (syn_cvv))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0003 p0004
  have p0006 :=
    @g_dfcleq z (.cv w) V dv_cache_0001 dv_cache_0002
  have p0007 :=
    @g_elima1c z (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) dv_cache_0003 dv_cache_0004
  have p0008 :=
    @g_elsymdif (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_cins2 (syn_csset)) (syn_cins3 R)
  have p0009 :=
    @g_vex x
  have p0010 :=
    @g_vex y
  have p0011 :=
    @g_opex (.cv x) (.cv y) p0009 p0010
  have p0012 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) (.cv w) (syn_csset) p0011
  have p0013 :=
    @g_vex z
  have p0014 :=
    @g_opelssetsn (.cv z) (.cv w) p0013 p0001
  have p0015_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv w)) (syn_csset)) (.objMem z w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0014
  have p0015 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (.cv w)) (syn_csset)) (.objMem z w) p0012 p0015_e01_recanon
  have p0016 :=
    @g_otelins3 (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) (.cv w) R p0001
  have p0017 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_cins3 R)) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) R) (.classMem (.cv z) V) p0016 hyp_releqmpt2_1
  have p0018 :=
    @g_bibi12i (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_cins2 (syn_csset))) (.objMem z w) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_cins3 R)) (.classMem (.cv z) V) p0015 p0017
  have p0019 :=
    @g_xchbinx (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R))) (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_cins3 R))) (syn_wb (.objMem z w) (.classMem (.cv z) V)) p0008 p0018
  have p0020 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R))) (.neg (syn_wb (.objMem z w) (.classMem (.cv z) V))) z p0019
  have p0021 :=
    @g_exnal (syn_wb (.objMem z w) (.classMem (.cv z) V)) z
  have p0022 :=
    @g_n_3bitri (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))) (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)))) (syn_wex z (.neg (syn_wb (.objMem z w) (.classMem (.cv z) V)))) (.neg (.all z (syn_wb (.objMem z w) (.classMem (.cv z) V)))) p0007 p0020 p0021
  have p0023 :=
    @g_con2bii (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))) (.all z (syn_wb (.objMem z w) (.classMem (.cv z) V))) p0022
  have p0024_e00_recanon : Nominal.NPrf (syn_wb (.classEq (.cv w) V) (.all z (syn_wb (.objMem z w) (.classMem (.cv z) V)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0024 :=
    @g_bitr2i (.classEq (.cv w) V) (.all z (syn_wb (.objMem z w) (.classMem (.cv z) V))) (.neg (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))) p0024_e00_recanon p0023
  have p0025 :=
    @g_anbi12i (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cxp (syn_cxp A B) (syn_cvv))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.neg (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))) (.classEq (.cv w) V) p0005 p0024
  have p0026 :=
    @g_bitri (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cxp (syn_cxp A B) (syn_cvv))) (.neg (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))))) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) V)) p0000 p0025
  have p0027 :=
    @g_oprabbi2i (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) V)) x y w (syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0026
  have p0028 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt2 x y w A B V dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0009 dv_cache_0010
  have p0029 :=
    @g_eqtr4i (syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))) (syn_coprab x y w (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) V))) (syn_cmpt2 x A y B V) p0027 p0028
  exact p0029

noncomputable def g_mptexlem
    (A : Class) (R : Class) (hyp_mptexlem_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_mptexlem_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    @g_vvex
  have p0001 :=
    @g_xpex A (syn_cvv) hyp_mptexlem_1 p0000
  have p0002 :=
    @g_ssetex
  have p0003 :=
    @g_ins3ex (syn_csset) p0002
  have p0004 :=
    @g_ins2ex R hyp_mptexlem_2
  have p0005 :=
    @g_symdifex (syn_cins3 (syn_csset)) (syn_cins2 R) p0003 p0004
  have p0006 :=
    @g_n_1cex
  have p0007 :=
    @g_imaex (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c) p0005 p0006
  have p0008 :=
    @g_complex (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)) p0007
  have p0009 :=
    @g_cnvex (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))) p0008
  have p0010 :=
    @g_inex (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))) p0001 p0009
  exact p0010

#print axioms g_mptexlem

end NFChoice.DirectNominalPrf.WPPReplay
