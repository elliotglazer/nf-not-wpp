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
import NominalWPPReplayChunk016Compact001Part005

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

noncomputable def g_wecutisouniondirectedndv
    (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_B_h : h ∉ B.fv) (dv_C_h : h ∉ C.fv) (dv_D_h : h ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_S_h : h ∉ S.fv) (hyp_wecutisouniondirectedndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisouniondirectedndv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.imp (syn_wa (.classMem C (syn_cuni (syn_cwecutiso R D S E))) (.classMem B (syn_cuni (syn_cwecutiso R D S E)))) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h))))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({h} : Finset Var) ∪ E.fv
  let f : Var := freshVar proofSupport 0
  let g : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_ne_h : f ≠ h := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_f : h ≠ f :=
    Ne.symm fresh_f_ne_h
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_g_not_D : g ∉ D.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_g_not_R : g ∉ R.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_g_not_S : g ∉ S.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_ne_h : g ≠ h := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_g : h ≠ g :=
    Ne.symm fresh_g_ne_h
  have fresh_g_not_E : g ∉ E.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_f_ne_g : f ≠ g := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_g_ne_f : g ≠ f :=
    Ne.symm fresh_f_ne_g
  have dv_cache_0001 : f ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((syn_cwecutiso R D S E)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((syn_cwecutiso R D S E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_D, fresh_g_not_E, fresh_g_not_R, fresh_g_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : h ∉ ((Class.cv g)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : h ∉ ((syn_cwecutiso R D S E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : h ∉ ((syn_wa (.classMem C (.cv g)) (.classMem B (.cv g)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_h, fresh_h_ne_g, dv_B_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : h ∉ ((Class.cv f)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : h ∉ ((syn_wa (.classMem C (.cv f)) (.classMem B (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_h, fresh_h_ne_f, dv_B_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : g ∉ ((syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_D, fresh_g_not_E, fresh_g_not_R, fresh_g_not_S, fresh_g_not_C, fresh_g_ne_h, fresh_g_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : g ∉ ((syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem C (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_f, fresh_g_not_D, fresh_g_not_E, fresh_g_not_R, fresh_g_not_S, fresh_g_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : f ∉ ((syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S, fresh_f_not_C, fresh_f_ne_h, fresh_f_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : f ∉ ((syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S, fresh_f_not_B, fresh_f_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem C (syn_cuni (syn_cwecutiso R D S E))) (.classMem B (syn_cuni (syn_cwecutiso R D S E)))
  have p0001 :=
    @g_eluni2 f C (syn_cwecutiso R D S E) dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_biimpi (.classMem C (syn_cuni (syn_cwecutiso R D S E))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem C (.cv f))) p0001
  have p0003 :=
    @g_syl (syn_wa (.classMem C (syn_cuni (syn_cwecutiso R D S E))) (.classMem B (syn_cuni (syn_cwecutiso R D S E)))) (.classMem C (syn_cuni (syn_cwecutiso R D S E))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem C (.cv f))) p0000 p0002
  have p0004 :=
    @g_simpr (.classMem C (syn_cuni (syn_cwecutiso R D S E))) (.classMem B (syn_cuni (syn_cwecutiso R D S E)))
  have p0005 :=
    @g_eluni2 g B (syn_cwecutiso R D S E) dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_biimpi (.classMem B (syn_cuni (syn_cwecutiso R D S E))) (syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g))) p0005
  have p0007 :=
    @g_syl (syn_wa (.classMem C (syn_cuni (syn_cwecutiso R D S E))) (.classMem B (syn_cuni (syn_cwecutiso R D S E)))) (.classMem B (syn_cuni (syn_cwecutiso R D S E))) (syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g))) p0004 p0006
  have p0008 :=
    @g_jca (syn_wa (.classMem C (syn_cuni (syn_cwecutiso R D S E))) (.classMem B (syn_cuni (syn_cwecutiso R D S E)))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem C (.cv f))) (syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g))) p0003 p0007
  have p0009 :=
    @g_simpl (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))
  have p0010 :=
    @g_simpr (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))
  have p0011 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (.classMem (.cv g) (syn_cwecutiso R D S E)) p0009 p0010
  have p0012 :=
    @g_a1d (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (.classMem (.cv g) (syn_cwecutiso R D S E)) (syn_wss (.cv f) (.cv g)) p0011
  have p0013 :=
    @g_simpr (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))
  have p0014 :=
    @g_simpl (.classMem C (.cv f)) (.classMem B (.cv g))
  have p0015 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g))) (.classMem C (.cv f)) p0013 p0014
  have p0016 :=
    @g_ssel (.cv f) (.cv g) C
  have p0017 :=
    @g_syl5com (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (.classMem C (.cv f)) (syn_wss (.cv f) (.cv g)) (.classMem C (.cv g)) p0015 p0016
  have p0018 :=
    @g_simpr (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))
  have p0019 :=
    @g_simpr (.classMem C (.cv f)) (.classMem B (.cv g))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g))) (.classMem B (.cv g)) p0018 p0019
  have p0021 :=
    @g_a1d (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (.classMem B (.cv g)) (syn_wss (.cv f) (.cv g)) p0020
  have p0022 :=
    @g_jcad (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wss (.cv f) (.cv g)) (.classMem C (.cv g)) (.classMem B (.cv g)) p0017 p0021
  have p0023 :=
    @g_jcad (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wss (.cv f) (.cv g)) (.classMem (.cv g) (syn_cwecutiso R D S E)) (syn_wa (.classMem C (.cv g)) (.classMem B (.cv g))) p0012 p0022
  have p0024 :=
    @g_eleq2 (.cv h) (.cv g) C
  have p0025 :=
    @g_eleq2 (.cv h) (.cv g) B
  have p0026 :=
    @g_anbi12d (.classEq (.cv h) (.cv g)) (.classMem C (.cv h)) (.classMem C (.cv g)) (.classMem B (.cv h)) (.classMem B (.cv g)) p0024 p0025
  have p0027 :=
    @g_rspcev (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h))) (syn_wa (.classMem C (.cv g)) (.classMem B (.cv g))) h (.cv g) (syn_cwecutiso R D S E) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0026
  have p0028 :=
    @g_syl6 (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wss (.cv f) (.cv g)) (syn_wa (.classMem (.cv g) (syn_cwecutiso R D S E)) (syn_wa (.classMem C (.cv g)) (.classMem B (.cv g)))) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) p0023 p0027
  have p0029 :=
    @g_simpl (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))
  have p0030 :=
    @g_simpl (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (.classMem (.cv f) (syn_cwecutiso R D S E)) p0029 p0030
  have p0032 :=
    @g_a1d (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wss (.cv g) (.cv f)) p0031
  have p0033 :=
    @g_simpr (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))
  have p0034 :=
    @g_simpl (.classMem C (.cv f)) (.classMem B (.cv g))
  have p0035 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g))) (.classMem C (.cv f)) p0033 p0034
  have p0036 :=
    @g_a1d (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (.classMem C (.cv f)) (syn_wss (.cv g) (.cv f)) p0035
  have p0037 :=
    @g_simpr (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))
  have p0038 :=
    @g_simpr (.classMem C (.cv f)) (.classMem B (.cv g))
  have p0039 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g))) (.classMem B (.cv g)) p0037 p0038
  have p0040 :=
    @g_ssel (.cv g) (.cv f) B
  have p0041 :=
    @g_syl5com (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (.classMem B (.cv g)) (syn_wss (.cv g) (.cv f)) (.classMem B (.cv f)) p0039 p0040
  have p0042 :=
    @g_jcad (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wss (.cv g) (.cv f)) (.classMem C (.cv f)) (.classMem B (.cv f)) p0036 p0041
  have p0043 :=
    @g_jcad (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wss (.cv g) (.cv f)) (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv f))) p0032 p0042
  have p0044 :=
    @g_eleq2 (.cv h) (.cv f) C
  have p0045 :=
    @g_eleq2 (.cv h) (.cv f) B
  have p0046 :=
    @g_anbi12d (.classEq (.cv h) (.cv f)) (.classMem C (.cv h)) (.classMem C (.cv f)) (.classMem B (.cv h)) (.classMem B (.cv f)) p0044 p0045
  have p0047 :=
    @g_rspcev (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv f))) h (.cv f) (syn_cwecutiso R D S E) dv_cache_0008 dv_cache_0006 dv_cache_0009 p0046
  have p0048 :=
    @g_syl6 (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wss (.cv g) (.cv f)) (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv f)))) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) p0043 p0047
  have p0049 :=
    @g_simpl (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))
  have p0050 :=
    @g_wecutisofamilychainndv D R S f g E hyp_wecutisouniondirectedndv_1 hyp_wecutisouniondirectedndv_2
  have p0051 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) p0049 p0050
  have p0052 :=
    @g_mpjaod (syn_wa (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E))) (syn_wa (.classMem C (.cv f)) (.classMem B (.cv g)))) (syn_wss (.cv f) (.cv g)) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) (syn_wss (.cv g) (.cv f)) p0028 p0048 p0051
  have p0053 :=
    @g_an4s (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv g) (syn_cwecutiso R D S E)) (.classMem C (.cv f)) (.classMem B (.cv g)) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) p0052
  have p0054 :=
    @g_exp32 (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem C (.cv f))) (.classMem (.cv g) (syn_cwecutiso R D S E)) (.classMem B (.cv g)) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) p0053
  have p0055 :=
    @g_rexlimdv (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem C (.cv f))) (.classMem B (.cv g)) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) g (syn_cwecutiso R D S E) dv_cache_0010 dv_cache_0011 p0054
  have p0056 :=
    @g_ex (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem C (.cv f)) (.imp (syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g))) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h))))) p0055
  have p0057 :=
    @g_com3r (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem C (.cv f)) (syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g))) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) p0056
  have p0058 :=
    @g_rexlimdv (syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g))) (.classMem C (.cv f)) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) f (syn_cwecutiso R D S E) dv_cache_0012 dv_cache_0013 p0057
  have p0059 :=
    @g_com12 (syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem C (.cv f))) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) p0058
  have p0060 :=
    @g_imp (syn_wrex f (syn_cwecutiso R D S E) (.classMem C (.cv f))) (syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g))) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) p0059
  have p0061 :=
    @g_syl (syn_wa (.classMem C (syn_cuni (syn_cwecutiso R D S E))) (.classMem B (syn_cuni (syn_cwecutiso R D S E)))) (syn_wa (syn_wrex f (syn_cwecutiso R D S E) (.classMem C (.cv f))) (syn_wrex g (syn_cwecutiso R D S E) (.classMem B (.cv g)))) (syn_wrex h (syn_cwecutiso R D S E) (syn_wa (.classMem C (.cv h)) (.classMem B (.cv h)))) p0008 p0060
  exact p0061

#print axioms g_wecutisouniondirectedndv

end NFChoice.DirectNominalPrf.WPPReplay
