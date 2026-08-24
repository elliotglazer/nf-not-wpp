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
import NominalWPPReplayChunk015Compact001Part040

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

noncomputable def g_isostrictsegresndv
    (x : Var) (D : Class) (R : Class) (S : Class) (E : Class) (H : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ H.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_H : u ∉ H.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_H : v ∉ H.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have dv_cache_0001 : v ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_D, fresh_v_not_R, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, fresh_u_not_E, fresh_u_not_H, fresh_u_not_R, fresh_u_not_S, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_D, fresh_v_not_E, fresh_v_not_H, fresh_v_not_R, fresh_v_not_S, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0005 : u ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, fresh_u_not_R, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_E, fresh_u_not_S, fresh_u_ne_x, fresh_u_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_E, fresh_v_not_S, fresh_v_ne_x, fresh_v_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_H, fresh_u_not_D, fresh_u_not_R, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : v ∉ ((syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_H, fresh_v_not_D, fresh_v_not_R, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : v ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0001 :=
    @g_isof1o D E R S H
  have p0002 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso H R S D E) (syn_wf1o H D E) p0000 p0001
  have p0003 :=
    @g_f1of1 D E H
  have p0004 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o H D E) (syn_wf1 H D E) p0002 p0003
  have p0005 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0006 :=
    @g_a1i (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D) (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) p0005
  have p0007 :=
    @g_jca (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1 H D E) (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D) p0004 p0006
  have p0008 :=
    @g_f1ores D E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0009 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (syn_wf1 H D E) (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D)) (syn_wf1o (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0007 p0008
  have p0010 :=
    @g_isostrictsegimandv x D R S E H
  have p0011 :=
    @g_f1oeq3 (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0012 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (.classEq (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wb (syn_wf1o (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) p0010 p0011
  have p0013 :=
    @g_mpbid (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) p0009 p0012
  have p0014 :=
    @g_simpl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0015 :=
    @g_simpl (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso H R S D E) p0014 p0015
  have p0017 :=
    @g_simpr (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0018 :=
    @g_simpl (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0017 p0018
  have p0020 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0021 :=
    @g_sseli (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D (.cv u) p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv u) D) p0019 p0021
  have p0023 :=
    @g_simpr (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0024 :=
    @g_simpr (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0023 p0024
  have p0026 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0027 :=
    @g_sseli (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D (.cv v) p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) D) p0025 p0027
  have p0029 :=
    @g_jca (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classMem (.cv u) D) (.classMem (.cv v) D) p0022 p0028
  have p0030 :=
    @g_jca (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wiso H R S D E) (syn_wa (.classMem (.cv u) D) (.classMem (.cv v) D)) p0016 p0029
  have p0031 :=
    @g_isorel D E (.cv u) (.cv v) R S H
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wa (syn_wiso H R S D E) (syn_wa (.classMem (.cv u) D) (.classMem (.cv v) D))) (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv H (.cv u)) S (syn_cfv H (.cv v)))) p0030 p0031
  have p0033 :=
    @g_simpr (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0034 :=
    @g_simpl (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0033 p0034
  have p0036 :=
    @g_fvres (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u)) (syn_cfv H (.cv u))) p0035 p0036
  have p0038 :=
    @g_simpr (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0039 :=
    @g_simpr (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0038 p0039
  have p0041 :=
    @g_fvres (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv v)) (syn_cfv H (.cv v))) p0040 p0041
  have p0043 :=
    @g_breq12d (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u)) (syn_cfv H (.cv u)) (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv v)) (syn_cfv H (.cv v)) S p0037 p0042
  have p0044 :=
    @g_bibi2d (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wbr (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u)) S (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv v))) (syn_wbr (syn_cfv H (.cv u)) S (syn_cfv H (.cv v))) (syn_wbr (.cv u) R (.cv v)) p0043
  have p0045 :=
    @g_mpbird (syn_wa (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv u) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv v) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u)) S (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv v)))) (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv H (.cv u)) S (syn_cfv H (.cv v)))) p0032 p0044
  have p0046 :=
    @g_ralrimivva (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u)) S (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv v)))) u v (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0045
  have p0047 :=
    @g_jca (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wral u (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wral v (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u)) S (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv v)))))) p0013 p0046
  have p0048 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso u v (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) R S (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) dv_cache_0005 dv_cache_0001 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0004
  have p0049 :=
    @g_sylibr (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (syn_wf1o (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wral u (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wral v (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wb (syn_wbr (.cv u) R (.cv v)) (syn_wbr (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv u)) S (syn_cfv (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.cv v))))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) p0047 p0048
  have p0050 :=
    @g_isores1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) R S (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0051 :=
    @g_sylib (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) p0049 p0050
  have p0052 :=
    @g_isores2 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) S (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0053 :=
    @g_sylib (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) p0051 p0052
  exact p0053

#print axioms g_isostrictsegresndv

end NFChoice.DirectNominalPrf.WPPReplay
