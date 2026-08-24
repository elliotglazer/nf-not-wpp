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
import NominalWPPReplayChunk016Compact001Part017

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

noncomputable def g_wecutisogenrawcl
    (A : Class) (B : Class) (C : Class) (f : Var) (r : Var) (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_B_f : f ∉ B.fv) (dv_B_r : r ∉ B.fv) (dv_C_f : f ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_f_r : f ≠ r) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ ({f} : Finset Var) ∪ ({r} : Finset Var)
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_ne_f : v ≠ f := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_v : f ≠ v :=
    Ne.symm fresh_v_ne_f
  have fresh_v_ne_r : v ≠ r := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_v : r ≠ v :=
    Ne.symm fresh_v_ne_r
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_u : f ≠ u :=
    Ne.symm fresh_u_ne_f
  have fresh_u_ne_r : u ≠ r := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_u : r ≠ u :=
    Ne.symm fresh_u_ne_r
  have fresh_v_ne_u : v ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have dv_cache_0001 : r ∉ ((Wff.classEq (.cv v) C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_v, dv_C_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((Wff.classEq (.cv u) B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_u, dv_B_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0006 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0007 : f ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show f ≠ v from (by exact fresh_f_ne_v))
  have dv_cache_0008 : r ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show r ≠ u from (by exact fresh_r_ne_u))
  have dv_cache_0009 : r ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show r ≠ v from (by exact fresh_r_ne_v))
  have dv_cache_0010 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0011 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((Wff.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A, fresh_u_ne_v, fresh_u_ne_f, fresh_u_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : v ∉ ((Wff.imp (.classMem B (syn_cvv)) (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_A, fresh_v_not_C, fresh_v_ne_f, fresh_v_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
  have p0001 :=
    @g_simpl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))
  have p0002 :=
    @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0003 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_chwcn A)) p0001 p0002
  have p0004 :=
    @g_elex B (syn_chwcn A)
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_simpl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))
  have p0007 :=
    @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0008 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem C (syn_chwcn A)) p0006 p0007
  have p0009 :=
    @g_elex C (syn_chwcn A)
  have p0010 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_biid (.classMem B (syn_chwcn A))
  have p0012 :=
    @g_a1i (syn_wb (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A))) (.classEq (.cv v) C) p0011
  have p0013 :=
    @g_id (.classEq (.cv v) C)
  have p0014 :=
    @g_eleq1d (.classEq (.cv v) C) (.cv v) C (syn_chwcn A) p0013
  have p0015 :=
    @g_anbi12d (.classEq (.cv v) C) (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem C (syn_chwcn A)) p0012 p0014
  have p0016 :=
    @g_id (.classEq (.cv v) C)
  have p0017 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c1st) p0016
  have p0018 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (.cv f)
  have p0019 :=
    @g_syl (.classEq (.cv v) C) (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C)) (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) p0017 p0018
  have p0020 :=
    @g_id (.classEq (.cv v) C)
  have p0021 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c2nd) p0020
  have p0022 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (.cv f)
  have p0023 :=
    @g_syl (.classEq (.cv v) C) (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C)) (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) p0021 p0022
  have p0024 :=
    @g_bitrd (.classEq (.cv v) C) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)) p0019 p0023
  have p0025 :=
    @g_anbi12d (.classEq (.cv v) C) (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)) p0015 p0024
  have p0026 :=
    @g_biid (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f)))
  have p0027 :=
    @g_a1i (syn_wb (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f)))) (.classEq (.cv v) C) p0026
  have p0028 :=
    @g_biid (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
  have p0029 :=
    @g_a1i (syn_wb (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)) (.classEq (.cv v) C) p0028
  have p0030 :=
    @g_id (.classEq (.cv v) C)
  have p0031 :=
    @g_eqeq2d (.classEq (.cv v) C) (.cv v) C (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) p0030
  have p0032 :=
    @g_anbi12d (.classEq (.cv v) C) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C) p0029 p0031
  have p0033 :=
    @g_anbi12d (.classEq (.cv v) C) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)) p0027 p0032
  have p0034 :=
    @g_rexbidv (.classEq (.cv v) C) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))) r (syn_cvv) dv_cache_0001 p0033
  have p0035 :=
    @g_imbi12d (.classEq (.cv v) C) (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))) p0025 p0034
  have p0036 :=
    @g_imbi2d (.classEq (.cv v) C) (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (.classMem B (syn_cvv)) p0035
  have p0037 :=
    @g_id (.classEq (.cv u) B)
  have p0038 :=
    @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0037
  have p0039 :=
    @g_biid (.classMem (.cv v) (syn_chwcn A))
  have p0040 :=
    @g_a1i (syn_wb (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classEq (.cv u) B) p0039
  have p0041 :=
    @g_anbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0038 p0040
  have p0042 :=
    @g_id (.classEq (.cv u) B)
  have p0043 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c1st) p0042
  have p0044 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B) (.cv f)
  have p0045 :=
    @g_syl (.classEq (.cv u) B) (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B)) (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0043 p0044
  have p0046 :=
    @g_id (.classEq (.cv u) B)
  have p0047 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0046
  have p0048 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (.cv f)
  have p0049 :=
    @g_syl (.classEq (.cv u) B) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B)) (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) p0047 p0048
  have p0050 :=
    @g_bitrd (.classEq (.cv u) B) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) p0045 p0049
  have p0051 :=
    @g_anbi12d (.classEq (.cv u) B) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) p0041 p0050
  have p0052 :=
    @g_biid (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f)))
  have p0053 :=
    @g_a1i (syn_wb (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f)))) (.classEq (.cv u) B) p0052
  have p0054 :=
    @g_id (.classEq (.cv u) B)
  have p0055 :=
    @g_eqeq2d (.classEq (.cv u) B) (.cv u) B (syn_cop (.cv r) (syn_cdm (.cv f))) p0054
  have p0056 :=
    @g_biid (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))
  have p0057 :=
    @g_a1i (syn_wb (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))) (.classEq (.cv u) B) p0056
  have p0058 :=
    @g_anbi12d (.classEq (.cv u) B) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)) p0055 p0057
  have p0059 :=
    @g_anbi12d (.classEq (.cv u) B) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))) p0053 p0058
  have p0060 :=
    @g_rexbidv (.classEq (.cv u) B) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))) r (syn_cvv) dv_cache_0002 p0059
  have p0061 :=
    @g_imbi12d (.classEq (.cv u) B) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) p0051 p0060
  have p0062 :=
    @g_hwnisorawgeni v u A f r dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0063 :=
    @g_vtoclg (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) u B (syn_cvv) dv_cache_0011 dv_cache_0012 p0061 p0062
  have p0064 :=
    @g_vtoclg (.imp (.classMem B (syn_cvv)) (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))))) (.imp (.classMem B (syn_cvv)) (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))))) v C (syn_cvv) dv_cache_0013 dv_cache_0014 p0036 p0063
  have p0065 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (.classMem C (syn_cvv)) (.imp (.classMem B (syn_cvv)) (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))))) p0010 p0064
  have p0066 :=
    @g_mpd (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (.classMem B (syn_cvv)) (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) p0005 p0065
  have p0067 :=
    @g_mpd (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))) p0000 p0066
  exact p0067

noncomputable def g_wecutisogencodeinran
    (x : Var) (D : Class) (R : Class) (hyp_wecutisogencodeinran_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_hnwcutrelfn D R hyp_wecutisogencodeinran_1
  have p0001 :=
    @g_a1i (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (.classMem (.cv x) D) p0000
  have p0002 :=
    @g_snelpw1 (.cv x) D
  have p0003 :=
    @g_biimpri (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0002
  have p0004 :=
    @g_jca (.classMem (.cv x) D) (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0001 p0003
  have p0005 :=
    @g_fnfvelrn (syn_cpw1 D) (syn_csn (.cv x)) (syn_chnwcutrel R D)
  have p0006 :=
    @g_syl (.classMem (.cv x) D) (syn_wa (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (.classMem (syn_csn (.cv x)) (syn_cpw1 D))) (.classMem (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))) (syn_crn (syn_chnwcutrel R D))) p0004 p0005
  have p0007 :=
    @g_hnwcutrelvalcld (.cv x) D R hyp_wecutisogencodeinran_1
  have p0008 :=
    @g_eleq1d (.classMem (.cv x) D) (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))) (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D)) p0007
  have p0009 :=
    @g_mpbid (.classMem (.cv x) D) (.classMem (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D))) p0006 p0008
  exact p0009

noncomputable def g_wecutisogenrangedecode
    (x : Var) (B : Class) (D : Class) (R : Class) (dv_B_x : x ∉ B.fv) (dv_D_x : x ∉ D.fv) (dv_R_x : x ∉ R.fv) (hyp_wecutisogenrangedecode_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem B (syn_crn (syn_chnwcutrel R D))) (syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ B.fv ∪ D.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((syn_cpw1 D)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_chnwcutrel R D)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, dv_D_x, dv_R_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, fresh_u_not_B, fresh_u_ne_x, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutrelfn D R hyp_wecutisogenrangedecode_1
  have p0001 :=
    @g_fvelrnb u (syn_cpw1 D) B (syn_chnwcutrel R D) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_biimpi (.classMem B (syn_crn (syn_chnwcutrel R D))) (syn_wrex u (syn_cpw1 D) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) p0002
  have p0004 :=
    @g_simpl (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)
  have p0005 :=
    @g_elpw1 x (.cv u) D dv_cache_0004 dv_cache_0005
  have p0006 :=
    @g_biimpi (.classMem (.cv u) (syn_cpw1 D)) (syn_wrex x D (.classEq (.cv u) (syn_csn (.cv x)))) p0005
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv u) (syn_cpw1 D)) (syn_wrex x D (.classEq (.cv u) (syn_csn (.cv x)))) p0004 p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))
  have p0009 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))) (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) p0008 p0009
  have p0011 :=
    @g_simpr (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))) (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B) p0010 p0011
  have p0013 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))) (syn_cfv (syn_chnwcutrel R D) (.cv u)) B p0012
  have p0014 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))
  have p0015 :=
    @g_id (.classEq (.cv u) (syn_csn (.cv x)))
  have p0016 :=
    @g_fveq2d (.classEq (.cv u) (syn_csn (.cv x))) (.cv u) (syn_csn (.cv x)) (syn_chnwcutrel R D) p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))) (.classEq (.cv u) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x)))) p0014 p0016
  have p0018 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))) B (syn_cfv (syn_chnwcutrel R D) (.cv u)) (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))) p0013 p0017
  have p0019 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))
  have p0020 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))) (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classMem (.cv x) D) p0019 p0020
  have p0022 :=
    @g_hnwcutrelvalcld (.cv x) D R hyp_wecutisogenrangedecode_1
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))) (.classMem (.cv x) D) (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))) (syn_chnwcutcode R D (.cv x))) p0021 p0022
  have p0024 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x)))) B (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))) (syn_chnwcutcode R D (.cv x)) p0018 p0023
  have p0025 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D)) (.classEq (.cv u) (syn_csn (.cv x))) (.classEq B (syn_chnwcutcode R D (.cv x))) p0024
  have p0026 :=
    @g_reximdva (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classEq (.cv u) (syn_csn (.cv x))) (.classEq B (syn_chnwcutcode R D (.cv x))) x D dv_cache_0006 p0025
  have p0027 :=
    @g_mpd (syn_wa (.classMem (.cv u) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (syn_wrex x D (.classEq (.cv u) (syn_csn (.cv x)))) (syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x)))) p0007 p0026
  have p0028 :=
    @g_rexlimiva (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B) (syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x)))) u (syn_cpw1 D) dv_cache_0007 p0027
  have p0029 :=
    @g_syl (.classMem B (syn_crn (syn_chnwcutrel R D))) (syn_wrex u (syn_cpw1 D) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x)))) p0003 p0028
  exact p0029

noncomputable def g_wecutisogencodeambient
    (x : Var) (D : Class) (R : Class) (hyp_wecutisogencodeambient_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_hnwcutcodecnndv x D R hyp_wecutisogencodeambient_1
  have p0001 :=
    @g_ssv D
  have p0002 :=
    @g_hwcnssbase (syn_cvv) D p0001
  have p0003 :=
    @g_sseli (syn_chwcn D) (syn_chwcn (syn_cvv)) (syn_chnwcutcode R D (.cv x)) p0002
  have p0004 :=
    @g_syl (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv))) p0000 p0003
  exact p0004

noncomputable def g_wecutisogennormbij
    (f : Var) (r : Var) :
    Nominal.NPrf (.imp (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (.classMem (.cv f) (syn_chwbij))) := by
  let proofSupport : Finset Var := ({f} : Finset Var) ∪ ({r} : Finset Var)
  have p0000 :=
    @g_hwtrnisob f r
  have p0001 :=
    @g_biimpri (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0000
  have p0002 :=
    @g_hwbijf1o f
  have p0003 :=
    @g_biimpri (.classMem (.cv f) (syn_chwbij)) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0002
  have p0004 :=
    @g_syl (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (.classMem (.cv f) (syn_chwbij)) p0001 p0003
  exact p0004

#print axioms g_wecutisogennormbij

end NFChoice.DirectNominalPrf.WPPReplay
