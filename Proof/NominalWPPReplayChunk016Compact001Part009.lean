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
import NominalWPPReplayChunk016Compact001Part008

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

noncomputable def g_wecutisomemberrndownndv
    (w : Var) (v : Var) (D : Class) (R : Class) (S : Class) (f : Var) (E : Class) (hyp_wecutisomemberrndownndv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (.classMem (.cv w) (syn_crn (.cv f)))) := by
  let proofSupport : Finset Var := ({w} : Finset Var) ∪ ({v} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({f} : Finset Var) ∪ E.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_w : x ≠ w := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_w : u ≠ w := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_w_ne_u : w ≠ u :=
    Ne.symm fresh_u_ne_w
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_u : f ≠ u :=
    Ne.symm fresh_u_ne_f
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0010 : f ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0011 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0012 : x ∉ ((Wff.imp (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (.classMem (.cv w) (syn_crn (.cv f))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, fresh_x_ne_f, fresh_x_ne_w, fresh_x_not_E, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : u ∉ ((Wff.imp (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (.classMem (.cv w) (syn_crn (.cv f))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_v, fresh_u_ne_f, fresh_u_ne_w, fresh_u_not_E, fresh_u_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have p0000 :=
    @g_elwecutisodmrn x u D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0001 :=
    @g_a1i (syn_wbr S (syn_cwe) E) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) hyp_wecutisomemberrndownndv_1
  have p0002 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
  have p0003 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0004 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (.classMem (.cv u) E) p0002 p0003
  have p0005 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wbr S (syn_cwe) E) (.classMem (.cv u) E) p0001 p0004
  have p0006 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
  have p0007 :=
    @g_simpr (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
  have p0008 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) p0006 p0007
  have p0009 :=
    @g_simpl (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
  have p0010 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (.classMem (.cv v) (syn_crn (.cv f))) p0008 p0009
  have p0011 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
  have p0012 :=
    @g_simpl (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0011 p0012
  have p0014 :=
    @g_simpr (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0015 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0013 p0014
  have p0016 :=
    @g_eleqtrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (.cv v) (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) p0010 p0015
  have p0017 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
  have p0018 :=
    @g_simpr (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
  have p0019 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) p0017 p0018
  have p0020 :=
    @g_simpr (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) p0019 p0020
  have p0022 :=
    @g_simpl (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) (.classMem (.cv w) E) p0021 p0022
  have p0024 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (.classMem (.cv w) E) p0016 p0023
  have p0025 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
  have p0026 :=
    @g_simpr (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
  have p0027 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) p0025 p0026
  have p0028 :=
    @g_simpr (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))
  have p0029 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) p0027 p0028
  have p0030 :=
    @g_simpr (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) (syn_wbr (.cv w) S (.cv v)) p0029 p0030
  have p0032 :=
    @g_n_3jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (syn_wbr S (syn_cwe) E) (.classMem (.cv u) E)) (syn_wa (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (.classMem (.cv w) E)) (syn_wbr (.cv w) S (.cv v)) p0005 p0024 p0031
  have p0033 :=
    @g_strictsegdown u v w E S
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_w3a (syn_wa (syn_wbr S (syn_cwe) E) (.classMem (.cv u) E)) (syn_wa (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (.classMem (.cv w) E)) (syn_wbr (.cv w) S (.cv v))) (.classMem (.cv w) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0032 p0033
  have p0035 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))
  have p0036 :=
    @g_simpl (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
  have p0037 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0035 p0036
  have p0038 :=
    @g_simpr (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0039 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0037 p0038
  have p0040 :=
    @g_eleqtrrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))))) (.cv w) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_crn (.cv f)) p0034 p0039
  have p0041 :=
    @g_exp32 (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (.classMem (.cv w) (syn_crn (.cv f))) p0040
  have p0042 :=
    @g_rexlimivv (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.imp (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (.classMem (.cv w) (syn_crn (.cv f)))) x u D E dv_cache_0001 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0041
  have p0043 :=
    @g_syl (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))) (.imp (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (.classMem (.cv w) (syn_crn (.cv f)))) p0000 p0042
  have p0044 :=
    @g_imp (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (.classMem (.cv w) (syn_crn (.cv f))) p0043
  exact p0044

noncomputable def g_wecutisouniondmdownndv
    (y : Var) (z : Var) (D : Class) (R : Class) (S : Class) (E : Class) (hyp_wecutisouniondmdownndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y)))) (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_ne_y : f ≠ y := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_f : y ≠ f :=
    Ne.symm fresh_f_ne_y
  have fresh_f_ne_z : f ≠ z := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_f : z ≠ f :=
    Ne.symm fresh_f_ne_z
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ ((syn_cwecutiso R D S E)).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.imp (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_z, fresh_f_not_D, fresh_f_ne_y, fresh_f_not_R, fresh_f_not_E, fresh_f_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dmuni f (syn_cwecutiso R D S E) dv_cache_0001
  have p0001 :=
    @g_eleq2i (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_ciun f (syn_cwecutiso R D S E) (syn_cdm (.cv f))) (.cv y) p0000
  have p0002 :=
    @g_eliun f (.cv y) (syn_cwecutiso R D S E) (syn_cdm (.cv f)) dv_cache_0002
  have p0003 :=
    @g_bitri (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (.classMem (.cv y) (syn_ciun f (syn_cwecutiso R D S E) (syn_cdm (.cv f)))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv y) (syn_cdm (.cv f)))) p0001 p0002
  have p0004 :=
    @g_biimpi (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv y) (syn_cdm (.cv f)))) p0003
  have p0005 :=
    @g_wecutisomemberdmdownndv y z D R S f E hyp_wecutisouniondmdownndv_1
  have p0006 :=
    @g_simpl (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv y) (syn_cdm (.cv f))) (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))))
  have p0007 :=
    @g_elssuni (.cv f) (syn_cwecutiso R D S E)
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv y) (syn_cdm (.cv f))) (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))))) (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wss (.cv f) (syn_cuni (syn_cwecutiso R D S E))) p0006 p0007
  have p0009 :=
    @g_dmss (.cv f) (syn_cuni (syn_cwecutiso R D S E))
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv y) (syn_cdm (.cv f))) (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))))) (syn_wss (.cv f) (syn_cuni (syn_cwecutiso R D S E))) (syn_wss (syn_cdm (.cv f)) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0008 p0009
  have p0011 :=
    @g_ssel (syn_cdm (.cv f)) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (.cv z)
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv y) (syn_cdm (.cv f))) (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))))) (syn_wss (syn_cdm (.cv f)) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (.imp (.classMem (.cv z) (syn_cdm (.cv f))) (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0010 p0011
  have p0013 :=
    @g_mpd (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv y) (syn_cdm (.cv f))) (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))))) (.classMem (.cv z) (syn_cdm (.cv f))) (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0005 p0012
  have p0014 :=
    @g_exp32 (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv y) (syn_cdm (.cv f))) (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0013
  have p0015 :=
    @g_rexlimiv (.classMem (.cv y) (syn_cdm (.cv f))) (.imp (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) f (syn_cwecutiso R D S E) dv_cache_0003 p0014
  have p0016 :=
    @g_syl (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv y) (syn_cdm (.cv f)))) (.imp (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0004 p0015
  have p0017 :=
    @g_imp (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_wa (.classMem (.cv z) D) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv z) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) p0016
  exact p0017

noncomputable def g_wecutisounionrndownndv
    (w : Var) (v : Var) (D : Class) (R : Class) (S : Class) (E : Class) (hyp_wecutisounionrndownndv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v)))) (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) := by
  let proofSupport : Finset Var := ({w} : Finset Var) ∪ ({v} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_ne_w : f ≠ w := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_w_ne_f : w ≠ f :=
    Ne.symm fresh_f_ne_w
  have fresh_f_ne_v : f ≠ v := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_v_ne_f : v ≠ f :=
    Ne.symm fresh_f_ne_v
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ ((syn_cwecutiso R D S E)).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.imp (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_w, fresh_f_not_E, fresh_f_ne_v, fresh_f_not_S, fresh_f_not_D, fresh_f_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_rnuni f (syn_cwecutiso R D S E) dv_cache_0001
  have p0001 :=
    @g_eleq2i (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_ciun f (syn_cwecutiso R D S E) (syn_crn (.cv f))) (.cv v) p0000
  have p0002 :=
    @g_eliun f (.cv v) (syn_cwecutiso R D S E) (syn_crn (.cv f)) dv_cache_0002
  have p0003 :=
    @g_bitri (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (.classMem (.cv v) (syn_ciun f (syn_cwecutiso R D S E) (syn_crn (.cv f)))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv v) (syn_crn (.cv f)))) p0001 p0002
  have p0004 :=
    @g_biimpi (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv v) (syn_crn (.cv f)))) p0003
  have p0005 :=
    @g_wecutisomemberrndownndv w v D R S f E hyp_wecutisounionrndownndv_1
  have p0006 :=
    @g_simpl (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))
  have p0007 :=
    @g_elssuni (.cv f) (syn_cwecutiso R D S E)
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wss (.cv f) (syn_cuni (syn_cwecutiso R D S E))) p0006 p0007
  have p0009 :=
    @g_rnss (.cv f) (syn_cuni (syn_cwecutiso R D S E))
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (syn_wss (.cv f) (syn_cuni (syn_cwecutiso R D S E))) (syn_wss (syn_crn (.cv f)) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0008 p0009
  have p0011 :=
    @g_ssel (syn_crn (.cv f)) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (.cv w)
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (syn_wss (syn_crn (.cv f)) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (.imp (.classMem (.cv w) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0010 p0011
  have p0013 :=
    @g_mpd (syn_wa (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wa (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))))) (.classMem (.cv w) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0005 p0012
  have p0014 :=
    @g_exp32 (.classMem (.cv f) (syn_cwecutiso R D S E)) (.classMem (.cv v) (syn_crn (.cv f))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0013
  have p0015 :=
    @g_rexlimiv (.classMem (.cv v) (syn_crn (.cv f))) (.imp (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) f (syn_cwecutiso R D S E) dv_cache_0003 p0014
  have p0016 :=
    @g_syl (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wrex f (syn_cwecutiso R D S E) (.classMem (.cv v) (syn_crn (.cv f)))) (.imp (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0004 p0015
  have p0017 :=
    @g_imp (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_wa (.classMem (.cv w) E) (syn_wbr (.cv w) S (.cv v))) (.classMem (.cv w) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0016
  exact p0017

#print axioms g_wecutisounionrndownndv

end NFChoice.DirectNominalPrf.WPPReplay
