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
import NominalWPPReplayChunk016Compact001Part035

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

noncomputable def g_wecomparisonterminalsetfdv
    (x : Var) (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_h : h ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_h_x : h ≠ x) (hyp_wecomparisonterminalsetfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecomparisonterminalsetfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) (hyp_wecomparisonterminalsetfdv_3 : Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({h} : Finset Var) ∪ E.fv
  let y : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_h : y ≠ h := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_y : h ≠ y :=
    Ne.symm fresh_y_ne_h
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_h : u ≠ h := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_u : h ≠ u :=
    Ne.symm fresh_u_ne_h
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have dv_cache_0001 : y ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (E).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : h ∉ ((syn_cuni (syn_cwecutiso R D S E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : h ∉ ((syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : h ∉ ((syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, dv_E_h, dv_S_h, fresh_h_ne_u, dv_R_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : h ∉ ((Wff.classEq (.cv x) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_h_x, fresh_h_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, dv_E_x, dv_S_x, fresh_x_ne_u, (Ne.symm dv_h_x), dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : u ∉ ((syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, fresh_u_not_E, fresh_u_not_R, fresh_u_ne_x, fresh_u_ne_h, fresh_u_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : u ∉ ((Wff.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, fresh_u_not_E, fresh_u_not_R, fresh_u_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : h ∉ ((syn_ccnv (syn_cuni (syn_cwecutiso R D S E)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : h ∉ ((syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_h, dv_D_h, dv_R_h, fresh_h_ne_y, dv_S_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : h ∉ ((Wff.classEq (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_h_x, fresh_h_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, dv_D_x, dv_R_x, fresh_x_ne_y, (Ne.symm dv_h_x), dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : h ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : h ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : h ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : h ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0031 : h ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show h ≠ x from (by exact dv_h_x))
  have dv_cache_0032 : h ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show h ≠ y from (by exact fresh_h_ne_y))
  have dv_cache_0033 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0034 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0035 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0036 : u ∉ ((syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_y, fresh_u_not_D, fresh_u_not_E, fresh_u_not_R, fresh_u_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : y ∉ ((syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_not_E, fresh_y_not_R, fresh_y_ne_x, fresh_y_ne_h, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wecutisouniondmcutorwholendv y D R S E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_wecomparisonterminalsetfdv_1 hyp_wecomparisonterminalsetfdv_3
  have p0001 :=
    @g_wecutisounionrncutorwholendv u D R S E dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 hyp_wecomparisonterminalsetfdv_2 hyp_wecomparisonterminalsetfdv_3
  have p0002 :=
    @g_a1i (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) p0001
  have p0003 :=
    @g_wecutisounionisondv D R S E hyp_wecomparisonterminalsetfdv_1 hyp_wecomparisonterminalsetfdv_2
  have p0004 :=
    @g_a1i (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) p0003
  have p0005 :=
    @g_simpl (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0006 :=
    @g_isoeq4 (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) D R S (syn_cuni (syn_cwecutiso R D S E))
  have p0007 :=
    @g_syl (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0005 p0006
  have p0008 :=
    @g_mpbid (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0004 p0007
  have p0009 :=
    @g_simpr (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0010 :=
    @g_isoeq5 D (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E R S (syn_cuni (syn_cwecutiso R D S E))
  have p0011 :=
    @g_syl (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E)) p0009 p0010
  have p0012 :=
    @g_mpbid (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E) p0008 p0011
  have p0013 :=
    @g_isoeq1 D E R S (syn_cuni (syn_cwecutiso R D S E)) (.cv h)
  have p0014 :=
    @g_spcev (syn_wiso (.cv h) R S D E) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E) h (syn_cuni (syn_cwecutiso R D S E)) dv_cache_0009 dv_cache_0010 hyp_wecomparisonterminalsetfdv_3 p0013
  have p0015 :=
    @g_syl (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E) (syn_wex h (syn_wiso (.cv h) R S D E)) p0012 p0014
  have p0016 :=
    @g_n_3mix1 (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0017 :=
    @g_syl (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0015 p0016
  have p0018 :=
    @g_ex (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0017
  have p0019 :=
    @g_simpl (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0020 :=
    @g_simpr (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classMem (.cv u) E) p0019 p0020
  have p0022 :=
    @g_wecutisounionisondv D R S E hyp_wecomparisonterminalsetfdv_1 hyp_wecomparisonterminalsetfdv_2
  have p0023 :=
    @g_a1i (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0022
  have p0024 :=
    @g_simpl (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0025 :=
    @g_simpl (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) p0024 p0025
  have p0027 :=
    @g_isoeq4 (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) D R S (syn_cuni (syn_cwecutiso R D S E))
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0026 p0027
  have p0029 :=
    @g_mpbid (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0023 p0028
  have p0030 :=
    @g_simpr (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0031 :=
    @g_isoeq5 D (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R S (syn_cuni (syn_cwecutiso R D S E))
  have p0032 :=
    @g_syl (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0030 p0031
  have p0033 :=
    @g_mpbid (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0029 p0032
  have p0034 :=
    @g_isores2 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R S (syn_cuni (syn_cwecutiso R D S E))
  have p0035 :=
    @g_biimpi (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0034
  have p0036 :=
    @g_syl (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0033 p0035
  have p0037 :=
    @g_isoeq1 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cuni (syn_cwecutiso R D S E)) (.cv h)
  have p0038 :=
    @g_spcev (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) h (syn_cuni (syn_cwecutiso R D S E)) dv_cache_0009 dv_cache_0011 hyp_wecomparisonterminalsetfdv_3 p0037
  have p0039 :=
    @g_syl (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0036 p0038
  have p0040 :=
    @g_jca (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv u) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0021 p0039
  have p0041 :=
    @g_sneq (.cv x) (.cv u)
  have p0042 :=
    @g_imaeq2d (.classEq (.cv x) (.cv u)) (syn_csn (.cv x)) (syn_csn (.cv u)) (syn_ccnv (syn_cdif S (syn_cid))) p0041
  have p0043 :=
    @g_ineq2d (.classEq (.cv x) (.cv u)) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))) E p0042
  have p0044 :=
    @g_sneq (.cv x) (.cv u)
  have p0045 :=
    @g_imaeq2d (.classEq (.cv x) (.cv u)) (syn_csn (.cv x)) (syn_csn (.cv u)) (syn_ccnv (syn_cdif S (syn_cid))) p0044
  have p0046 :=
    @g_ineq2d (.classEq (.cv x) (.cv u)) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))) E p0045
  have p0047 :=
    @g_xpeq12d (.classEq (.cv x) (.cv u)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) p0043 p0046
  have p0048 :=
    @g_ineq2d (.classEq (.cv x) (.cv u)) (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) S p0047
  have p0049 :=
    @g_isoeq3 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.cv h)
  have p0050 :=
    @g_syl (.classEq (.cv x) (.cv u)) (.classEq (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) (syn_wb (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) p0048 p0049
  have p0051 :=
    @g_sneq (.cv x) (.cv u)
  have p0052 :=
    @g_imaeq2d (.classEq (.cv x) (.cv u)) (syn_csn (.cv x)) (syn_csn (.cv u)) (syn_ccnv (syn_cdif S (syn_cid))) p0051
  have p0053 :=
    @g_ineq2d (.classEq (.cv x) (.cv u)) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))) E p0052
  have p0054 :=
    @g_isoeq5 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.cv h)
  have p0055 :=
    @g_syl (.classEq (.cv x) (.cv u)) (.classEq (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wb (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0053 p0054
  have p0056 :=
    @g_bitrd (.classEq (.cv x) (.cv u)) (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0050 p0055
  have p0057 :=
    @g_exbidv (.classEq (.cv x) (.cv u)) (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) h dv_cache_0012 p0056
  have p0058 :=
    @g_rspcev (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) x (.cv u) E dv_cache_0013 dv_cache_0014 dv_cache_0015 p0057
  have p0059 :=
    @g_syl (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv u) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) p0040 p0058
  have p0060 :=
    @g_n_3mix2 (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0061 :=
    @g_syl (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0059 p0060
  have p0062 :=
    @g_ex (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0061
  have p0063 :=
    @g_rexlimdva (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) u E dv_cache_0016 dv_cache_0017 p0062
  have p0064 :=
    @g_jaod (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0018 p0063
  have p0065 :=
    @g_mpd (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0002 p0064
  have p0066 :=
    @g_wecutisounionrncutorwholendv u D R S E dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 hyp_wecomparisonterminalsetfdv_2 hyp_wecomparisonterminalsetfdv_3
  have p0067 :=
    @g_a1i (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0066
  have p0068 :=
    @g_simpl (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0069 :=
    @g_simpl (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0070 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv y) D) p0068 p0069
  have p0071 :=
    @g_wecutisounionisondv D R S E hyp_wecomparisonterminalsetfdv_1 hyp_wecomparisonterminalsetfdv_2
  have p0072 :=
    @g_a1i (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) p0071
  have p0073 :=
    @g_simpl (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0074 :=
    @g_simpr (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0075 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0073 p0074
  have p0076 :=
    @g_isoeq4 (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) R S (syn_cuni (syn_cwecutiso R D S E))
  have p0077 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0075 p0076
  have p0078 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0072 p0077
  have p0079 :=
    @g_simpr (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0080 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E R S (syn_cuni (syn_cwecutiso R D S E))
  have p0081 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) E)) p0079 p0080
  have p0082 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) E) p0078 p0081
  have p0083 :=
    @g_isocnv (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) E R S (syn_cuni (syn_cwecutiso R D S E))
  have p0084 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) E) (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0082 p0083
  have p0085 :=
    @g_isores2 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) S R (syn_ccnv (syn_cuni (syn_cwecutiso R D S E)))
  have p0086 :=
    @g_biimpi (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0085
  have p0087 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0084 p0086
  have p0088 :=
    @g_cnvex (syn_cuni (syn_cwecutiso R D S E)) hyp_wecomparisonterminalsetfdv_3
  have p0089 :=
    @g_isoeq1 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) (.cv h)
  have p0090 :=
    @g_spcev (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) h (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) dv_cache_0018 dv_cache_0019 p0088 p0089
  have p0091 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0087 p0090
  have p0092 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (.classMem (.cv y) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0070 p0091
  have p0093 :=
    @g_sneq (.cv x) (.cv y)
  have p0094 :=
    @g_imaeq2d (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_ccnv (syn_cdif R (syn_cid))) p0093
  have p0095 :=
    @g_ineq2d (.classEq (.cv x) (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) D p0094
  have p0096 :=
    @g_sneq (.cv x) (.cv y)
  have p0097 :=
    @g_imaeq2d (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_ccnv (syn_cdif R (syn_cid))) p0096
  have p0098 :=
    @g_ineq2d (.classEq (.cv x) (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) D p0097
  have p0099 :=
    @g_xpeq12d (.classEq (.cv x) (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0095 p0098
  have p0100 :=
    @g_ineq2d (.classEq (.cv x) (.cv y)) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) R p0099
  have p0101 :=
    @g_isoeq3 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.cv h)
  have p0102 :=
    @g_syl (.classEq (.cv x) (.cv y)) (.classEq (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wb (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0100 p0101
  have p0103 :=
    @g_sneq (.cv x) (.cv y)
  have p0104 :=
    @g_imaeq2d (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_ccnv (syn_cdif R (syn_cid))) p0103
  have p0105 :=
    @g_ineq2d (.classEq (.cv x) (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) D p0104
  have p0106 :=
    @g_isoeq5 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.cv h)
  have p0107 :=
    @g_syl (.classEq (.cv x) (.cv y)) (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wb (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0105 p0106
  have p0108 :=
    @g_bitrd (.classEq (.cv x) (.cv y)) (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0102 p0107
  have p0109 :=
    @g_exbidv (.classEq (.cv x) (.cv y)) (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) h dv_cache_0020 p0108
  have p0110 :=
    @g_rspcev (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) x (.cv y) D dv_cache_0021 dv_cache_0022 dv_cache_0023 p0109
  have p0111 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wa (.classMem (.cv y) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0092 p0110
  have p0112 :=
    @g_n_3mix3 (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
  have p0113 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0111 p0112
  have p0114 :=
    @g_ex (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0113
  have p0115 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0116 :=
    @g_simpl (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)
  have p0117 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0115 p0116
  have p0118 :=
    @g_simpl (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0119 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv y) D) p0117 p0118
  have p0120 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0121 :=
    @g_simpr (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)
  have p0122 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classMem (.cv u) E) p0120 p0121
  have p0123 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv y) D) (.classMem (.cv u) E) p0119 p0122
  have p0124 :=
    @g_strictsegnel y D R
  have p0125 :=
    @g_a1i (.neg (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0124
  have p0126 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0127 :=
    @g_simpl (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)
  have p0128 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0126 p0127
  have p0129 :=
    @g_simpr (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0130 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0128 p0129
  have p0131 :=
    @g_eleq2d (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv y) p0130
  have p0132 :=
    @g_notbid (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0131
  have p0133 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.neg (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0125 p0132
  have p0134 :=
    @g_a1i (syn_wbr R (syn_cwe) D) (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) hyp_wecomparisonterminalsetfdv_1
  have p0135 :=
    @g_a1i (syn_wbr S (syn_cwe) E) (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) hyp_wecomparisonterminalsetfdv_2
  have p0136 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E) p0134 p0135
  have p0137 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0138 :=
    @g_simpl (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)
  have p0139 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0137 p0138
  have p0140 :=
    @g_simpl (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0141 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv y) D) p0139 p0140
  have p0142 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0143 :=
    @g_simpr (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)
  have p0144 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classMem (.cv u) E) p0142 p0143
  have p0145 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv y) D) (.classMem (.cv u) E) p0141 p0144
  have p0146 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E)) (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) p0136 p0145
  have p0147 :=
    @g_wecutisounionisondv D R S E hyp_wecomparisonterminalsetfdv_1 hyp_wecomparisonterminalsetfdv_2
  have p0148 :=
    @g_a1i (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0147
  have p0149 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0150 :=
    @g_simpl (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)
  have p0151 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0149 p0150
  have p0152 :=
    @g_simpr (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0153 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0151 p0152
  have p0154 :=
    @g_isoeq4 (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) R S (syn_cuni (syn_cwecutiso R D S E))
  have p0155 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0153 p0154
  have p0156 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0148 p0155
  have p0157 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0158 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R S (syn_cuni (syn_cwecutiso R D S E))
  have p0159 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0157 p0158
  have p0160 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0156 p0159
  have p0161 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E)) (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0146 p0160
  have p0162 :=
    @g_wecutisoaddpairisondv y u D R S E (syn_cuni (syn_cwecutiso R D S E))
  have p0163 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E)) (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))) (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0161 p0162
  have p0164 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0133 p0163
  have p0165 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))) p0123 p0164
  have p0166 :=
    @g_wecutisoextendedterminaldfdv x y u D R S h E dv_cache_0024 dv_cache_0005 dv_cache_0022 dv_cache_0001 dv_cache_0025 dv_cache_0006 dv_cache_0014 dv_cache_0002 dv_cache_0026 dv_cache_0007 dv_cache_0027 dv_cache_0003 dv_cache_0028 dv_cache_0008 dv_cache_0029 dv_cache_0004 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 hyp_wecomparisonterminalsetfdv_1 hyp_wecomparisonterminalsetfdv_2 hyp_wecomparisonterminalsetfdv_3
  have p0167 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0165 p0166
  have p0168 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0167
  have p0169 :=
    @g_rexlimdva (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) u E dv_cache_0016 dv_cache_0036 p0168
  have p0170 :=
    @g_jaod (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0114 p0169
  have p0171 :=
    @g_mpd (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0067 p0170
  have p0172 :=
    @g_ex (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0171
  have p0173 :=
    @g_rexlimiv (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) y D dv_cache_0037 p0172
  have p0174 :=
    @g_jaoi (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0065 p0173
  have p0175 :=
    Nominal.mp p0000 p0174
  exact p0175

#print axioms g_wecomparisonterminalsetfdv

end NFChoice.DirectNominalPrf.WPPReplay
