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
import NominalWPPReplayChunk013Compact001Part035

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

noncomputable def g_enmap2lem1
    (A : Class) (G : Class) (W : Class) (s : Var) (r : Var) (dv_A_s : s ∉ A.fv) (dv_G_s : s ∉ G.fv) (dv_r_s : r ≠ s) (hyp_enmap2lem1_1 : Nominal.NPrf (.classEq W (syn_cmpt s (syn_co G (syn_cmap) A) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf (.classMem W (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ G.fv ∪ W.fv ∪ ({s} : Finset Var) ∪ ({r} : Finset Var)
  let x : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_s : x ≠ s := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_x : s ≠ x :=
    Ne.symm fresh_x_ne_s
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_p_not_G : p ∉ G.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_W : p ∉ W.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_ne_s : p ≠ s := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_p : s ≠ p :=
    Ne.symm fresh_p_ne_s
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_p : r ≠ p :=
    Ne.symm fresh_p_ne_r
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have dv_cache_0001 : x ∉ ((syn_co G (syn_cmap) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ccom (.cv s) (syn_ccnv (.cv r)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_s, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : s ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show s ≠ x from (by exact fresh_s_ne_x))
  have dv_cache_0004 : x ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cop (.cv s) (syn_ccnv (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_s, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, fresh_x_ne_s, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((syn_cop (.cv s) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_s, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_ccompose)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompose, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_s, fresh_p_ne_r, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : s ∉ ((syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompose, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_r_s), dv_G_s, dv_A_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompose, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_G, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt s x (syn_co G (syn_cmap) A) (syn_ccom (.cv s) (syn_ccnv (.cv r))) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_opelres (.cv s) (.cv x) (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A)
  have p0002 :=
    @g_trtxp (.cv p) (.cv s) (.cv x) (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)
  have p0003 :=
    @g_brco x (.cv p) (.cv s) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @g_ancom (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (.cv s))
  have p0005 :=
    @g_brin (.cv x) (.cv s) (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))
  have p0006 :=
    @g_vex s
  have p0007 :=
    @g_brxp (.cv x) (.cv s) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)
  have p0008 :=
    @g_mpbiran2 (syn_wbr (.cv x) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)) (.cv s)) (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))) (.classMem (.cv s) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_eliniseg (syn_c2nd) (syn_ccnv (.cv r)) (.cv x)
  have p0010 :=
    @g_bitri (syn_wbr (.cv x) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)) (.cv s)) (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))) (syn_wbr (.cv x) (syn_c2nd) (syn_ccnv (.cv r))) p0008 p0009
  have p0011 :=
    @g_anbi2i (syn_wbr (.cv x) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)) (.cv s)) (syn_wbr (.cv x) (syn_c2nd) (syn_ccnv (.cv r))) (syn_wbr (.cv x) (syn_c1st) (.cv s)) p0010
  have p0012 :=
    @g_vex r
  have p0013 :=
    @g_cnvex (.cv r) p0012
  have p0014 :=
    @g_op1st2nd (.cv s) (syn_ccnv (.cv r)) (.cv x) p0006 p0013
  have p0015 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (.cv s)) (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv s)) (syn_wbr (.cv x) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)) (.cv s))) (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv s)) (syn_wbr (.cv x) (syn_c2nd) (syn_ccnv (.cv r)))) (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r)))) p0005 p0011 p0014
  have p0016 :=
    @g_anbi1i (syn_wbr (.cv x) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (.cv s)) (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r)))) (syn_wbr (.cv p) (syn_c1st) (.cv x)) p0015
  have p0017 :=
    @g_bitri (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (.cv s))) (syn_wa (syn_wbr (.cv x) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (.cv s)) (syn_wbr (.cv p) (syn_c1st) (.cv x))) (syn_wa (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r)))) (syn_wbr (.cv p) (syn_c1st) (.cv x))) p0004 p0016
  have p0018 :=
    @g_exbii (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (.cv s))) (syn_wa (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r)))) (syn_wbr (.cv p) (syn_c1st) (.cv x))) x p0017
  have p0019 :=
    @g_opex (.cv s) (syn_ccnv (.cv r)) p0006 p0013
  have p0020 :=
    @g_breq2 (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv p) (syn_c1st)
  have p0021 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r)))) x (syn_cop (.cv s) (syn_ccnv (.cv r))) dv_cache_0008 dv_cache_0009 p0019 p0020
  have p0022 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (.cv s)) (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (.cv s)))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r)))) (syn_wbr (.cv p) (syn_c1st) (.cv x)))) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r)))) p0003 p0018 p0021
  have p0023 :=
    @g_anbi1i (syn_wbr (.cv p) (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (.cv s)) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r)))) (syn_wbr (.cv p) (syn_c2nd) (.cv x)) p0022
  have p0024 :=
    @g_vex x
  have p0025 :=
    @g_op1st2nd (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x) (.cv p) p0019 p0024
  have p0026 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_cop (.cv s) (.cv x))) (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (.cv s)) (syn_wbr (.cv p) (syn_c2nd) (.cv x))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r)))) (syn_wbr (.cv p) (syn_c2nd) (.cv x))) (.classEq (.cv p) (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x))) p0002 p0023 p0025
  have p0027 :=
    @g_rexbii (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_cop (.cv s) (.cv x))) (.classEq (.cv p) (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x))) p (syn_ccompose) p0026
  have p0028 :=
    @g_elima p (syn_cop (.cv s) (.cv x)) (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose) dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0029 :=
    @g_risset p (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x)) (syn_ccompose) dv_cache_0013 dv_cache_0012
  have p0030 :=
    @g_n_3bitr4i (syn_wrex p (syn_ccompose) (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_cop (.cv s) (.cv x)))) (syn_wrex p (syn_ccompose) (.classEq (.cv p) (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x)))) (.classMem (syn_cop (.cv s) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose))) (.classMem (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x)) (syn_ccompose)) p0027 p0028 p0029
  have p0031 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cop (.cv s) (syn_ccnv (.cv r))) (syn_ccompose) (.cv x))))
  have p0032 :=
    @g_brcomposeg (.cv s) (syn_ccnv (.cv r)) (.cv x) (syn_cvv) (syn_cvv)
  have p0033 :=
    @g_mp2an (.classMem (.cv s) (syn_cvv)) (.classMem (syn_ccnv (.cv r)) (syn_cvv)) (syn_wb (syn_wbr (syn_cop (.cv s) (syn_ccnv (.cv r))) (syn_ccompose) (.cv x)) (.classEq (syn_ccom (.cv s) (syn_ccnv (.cv r))) (.cv x))) p0006 p0013 p0032
  have p0034 :=
    @g_eqcom (syn_ccom (.cv s) (syn_ccnv (.cv r))) (.cv x)
  have p0035 :=
    @g_bitri (syn_wbr (syn_cop (.cv s) (syn_ccnv (.cv r))) (syn_ccompose) (.cv x)) (.classEq (syn_ccom (.cv s) (syn_ccnv (.cv r))) (.cv x)) (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) p0033 p0034
  have p0036 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv s) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose))) (.classMem (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x)) (syn_ccompose)) (syn_wbr (syn_cop (.cv s) (syn_ccnv (.cv r))) (syn_ccompose) (.cv x)) (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) p0030 p0031 p0035
  have p0037 :=
    @g_anbi2ci (.classMem (syn_cop (.cv s) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose))) (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) (.classMem (.cv s) (syn_co G (syn_cmap) A)) p0036
  have p0038 :=
    @g_bitri (.classMem (syn_cop (.cv s) (.cv x)) (syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A))) (syn_wa (.classMem (syn_cop (.cv s) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose))) (.classMem (.cv s) (syn_co G (syn_cmap) A))) (syn_wa (.classMem (.cv s) (syn_co G (syn_cmap) A)) (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r))))) p0001 p0037
  have p0039 :=
    @g_opabbi2i (syn_wa (.classMem (.cv s) (syn_co G (syn_cmap) A)) (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r))))) s x (syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A)) dv_cache_0014 dv_cache_0015 dv_cache_0003 p0038
  have p0040 :=
    @g_n_3eqtr4i (syn_cmpt s (syn_co G (syn_cmap) A) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) (syn_copab s x (syn_wa (.classMem (.cv s) (syn_co G (syn_cmap) A)) (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) W (syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A)) p0000 hyp_enmap2lem1_1 p0039
  have p0041 :=
    @g_n_1stex
  have p0042 :=
    @g_n_2ndex
  have p0043 :=
    @g_cnvex (syn_c2nd) p0042
  have p0044 :=
    @g_snex (syn_ccnv (.cv r))
  have p0045 :=
    @g_imaex (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))) p0043 p0044
  have p0046 :=
    @g_vvex
  have p0047 :=
    @g_xpex (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv) p0045 p0046
  have p0048 :=
    @g_inex (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)) p0041 p0047
  have p0049 :=
    @g_n_1stex
  have p0050 :=
    @g_coex (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st) p0048 p0049
  have p0051 :=
    @g_n_2ndex
  have p0052 :=
    @g_txpex (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd) p0050 p0051
  have p0053 :=
    @g_composeex
  have p0054 :=
    @g_imaex (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose) p0052 p0053
  have p0055 :=
    @g_ovex G A (syn_cmap)
  have p0056 :=
    @g_resex (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A) p0054 p0055
  have p0057 :=
    @g_eqeltri W (syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A)) (syn_cvv) p0040 p0056
  exact p0057

noncomputable def g_enmap2lem2
    (G : Class) (W : Class) (s : Var) (r : Var) (a : Var) (dv_G_s : s ∉ G.fv) (dv_a_s : a ≠ s) (hyp_enmap2lem2_1 : Nominal.NPrf (.classEq W (syn_cmpt s (syn_co G (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf (syn_wfn W (syn_co G (syn_cmap) (.cv a))) := by
  let proofSupport : Finset Var := G.fv ∪ W.fv ∪ ({s} : Finset Var) ∪ ({r} : Finset Var) ∪ ({a} : Finset Var)
  have dv_cache_0001 : s ∉ ((syn_co G (syn_cmap) (.cv a))).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_s, (Ne.symm dv_a_s), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fnmpt s (syn_co G (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))) W (syn_cvv) dv_cache_0001 hyp_enmap2lem2_1
  have p0001 :=
    @g_vex s
  have p0002 :=
    @g_vex r
  have p0003 :=
    @g_cnvex (.cv r) p0002
  have p0004 :=
    @g_coex (.cv s) (syn_ccnv (.cv r)) p0001 p0003
  have p0005 :=
    @g_a1i (.classMem (syn_ccom (.cv s) (syn_ccnv (.cv r))) (syn_cvv)) (.classMem (.cv s) (syn_co G (syn_cmap) (.cv a))) p0004
  have p0006 :=
    @g_mprg (.classMem (syn_ccom (.cv s) (syn_ccnv (.cv r))) (syn_cvv)) (syn_wfn W (syn_co G (syn_cmap) (.cv a))) s (syn_co G (syn_cmap) (.cv a)) p0000 p0005
  exact p0006

noncomputable def g_enmap2lem3
    (S : Class) (T : Class) (G : Class) (W : Class) (s : Var) (r : Var) (a : Var) (b : Var) (dv_G_s : s ∉ G.fv) (dv_S_s : s ∉ S.fv) (dv_a_s : a ≠ s) (dv_r_s : r ≠ s) (hyp_enmap2lem3_1 : Nominal.NPrf (.classEq W (syn_cmpt s (syn_co G (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf (.imp (syn_wf1o (.cv r) (.cv a) (.cv b)) (.imp (syn_wbr S W T) (.classEq S (syn_ccom T (.cv r))))) := by
  let proofSupport : Finset Var := S.fv ∪ T.fv ∪ G.fv ∪ W.fv ∪ ({s} : Finset Var) ∪ ({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ({b} : Finset Var)
  have dv_cache_0001 : s ∉ (G).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ≠ s := by
    clear dv_cache_0001
    exact (show a ≠ s from (by exact dv_a_s))
  have dv_cache_0003 : s ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((syn_ccom S (syn_ccnv (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_s, (Ne.symm dv_r_s), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : s ∉ ((syn_co G (syn_cmap) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_s, (Ne.symm dv_a_s), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_breldm S T W
  have p0001 :=
    @g_enmap2lem2 G W s r a dv_cache_0001 dv_cache_0002 hyp_enmap2lem3_1
  have p0002 :=
    @g_fndm (syn_co G (syn_cmap) (.cv a)) W
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_syl6eleq (syn_wbr S W T) S (syn_cdm W) (syn_co G (syn_cmap) (.cv a)) p0000 p0003
  have p0005 :=
    @g_fnbrfvb (syn_co G (syn_cmap) (.cv a)) S T W
  have p0006 :=
    @g_mpan (syn_wfn W (syn_co G (syn_cmap) (.cv a))) (.classMem S (syn_co G (syn_cmap) (.cv a))) (syn_wb (.classEq (syn_cfv W S) T) (syn_wbr S W T)) p0001 p0005
  have p0007 :=
    @g_vex r
  have p0008 :=
    @g_cnvex (.cv r) p0007
  have p0009 :=
    @g_coexg S (syn_ccnv (.cv r)) (syn_co G (syn_cmap) (.cv a)) (syn_cvv)
  have p0010 :=
    @g_mpan2 (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classMem (syn_ccnv (.cv r)) (syn_cvv)) (.classMem (syn_ccom S (syn_ccnv (.cv r))) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_coeq1 (.cv s) S (syn_ccnv (.cv r))
  have p0012 :=
    @g_fvmptg s S (syn_ccom (.cv s) (syn_ccnv (.cv r))) (syn_ccom S (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv a)) (syn_cvv) W dv_cache_0003 dv_cache_0004 dv_cache_0005 p0011 hyp_enmap2lem3_1
  have p0013 :=
    @g_mpdan (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classMem (syn_ccom S (syn_ccnv (.cv r))) (syn_cvv)) (.classEq (syn_cfv W S) (syn_ccom S (syn_ccnv (.cv r)))) p0010 p0012
  have p0014 :=
    @g_eqeq1d (.classMem S (syn_co G (syn_cmap) (.cv a))) (syn_cfv W S) (syn_ccom S (syn_ccnv (.cv r))) T p0013
  have p0015 :=
    @g_eqcom (syn_ccom S (syn_ccnv (.cv r))) T
  have p0016 :=
    @g_syl6bb (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classEq (syn_cfv W S) T) (.classEq (syn_ccom S (syn_ccnv (.cv r))) T) (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0014 p0015
  have p0017 :=
    @g_biimpd (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classEq (syn_cfv W S) T) (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0016
  have p0018 :=
    @g_sylbird (.classMem S (syn_co G (syn_cmap) (.cv a))) (syn_wbr S W T) (.classEq (syn_cfv W S) T) (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0006 p0017
  have p0019 :=
    @g_mpcom (.classMem S (syn_co G (syn_cmap) (.cv a))) (syn_wbr S W T) (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0004 p0018
  have p0020 :=
    @g_jca (syn_wbr S W T) (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0004 p0019
  have p0021 :=
    @g_f1ococnv1 (.cv a) (.cv b) (.cv r)
  have p0022 :=
    @g_coeq2d (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_ccom (syn_ccnv (.cv r)) (.cv r)) (syn_cres (syn_cid) (.cv a)) S p0021
  have p0023 :=
    @g_adantr (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classEq (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r))) (syn_ccom S (syn_cres (syn_cid) (.cv a)))) (.classMem S (syn_co G (syn_cmap) (.cv a))) p0022
  have p0024 :=
    @g_elmapi S G (.cv a)
  have p0025 :=
    @g_fcoi1 (.cv a) G S
  have p0026 :=
    @g_syl (.classMem S (syn_co G (syn_cmap) (.cv a))) (syn_wf S (.cv a) G) (.classEq (syn_ccom S (syn_cres (syn_cid) (.cv a))) S) p0024 p0025
  have p0027 :=
    @g_adantl (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classEq (syn_ccom S (syn_cres (syn_cid) (.cv a))) S) (syn_wf1o (.cv r) (.cv a) (.cv b)) p0026
  have p0028 :=
    @g_eqtr2d (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem S (syn_co G (syn_cmap) (.cv a)))) (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r))) (syn_ccom S (syn_cres (syn_cid) (.cv a))) S p0023 p0027
  have p0029 :=
    @g_coeq1 T (syn_ccom S (syn_ccnv (.cv r))) (.cv r)
  have p0030 :=
    @g_coass S (syn_ccnv (.cv r)) (.cv r)
  have p0031 :=
    @g_syl6eq (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) (syn_ccom T (.cv r)) (syn_ccom (syn_ccom S (syn_ccnv (.cv r))) (.cv r)) (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r))) p0029 p0030
  have p0032 :=
    @g_eqeq2d (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) (syn_ccom T (.cv r)) (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r))) S p0031
  have p0033 :=
    @g_syl5ibrcom (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem S (syn_co G (syn_cmap) (.cv a)))) (.classEq S (syn_ccom T (.cv r))) (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) (.classEq S (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r)))) p0028 p0032
  have p0034 :=
    @g_expimpd (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) (.classEq S (syn_ccom T (.cv r))) p0033
  have p0035 :=
    @g_syl5 (syn_wbr S W T) (syn_wa (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classEq T (syn_ccom S (syn_ccnv (.cv r))))) (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classEq S (syn_ccom T (.cv r))) p0020 p0034
  exact p0035

noncomputable def g_enmap2lem4
    (G : Class) (W : Class) (s : Var) (r : Var) (a : Var) (b : Var) (dv_G_s : s ∉ G.fv) (dv_a_s : a ≠ s) (dv_r_s : r ≠ s) (hyp_enmap2lem4_1 : Nominal.NPrf (.classEq W (syn_cmpt s (syn_co G (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf (.imp (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wfun (syn_ccnv W))) := by
  let proofSupport : Finset Var := G.fv ∪ W.fv ∪ ({s} : Finset Var) ∪ ({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ({b} : Finset Var)
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_ne_s : y ≠ s := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_s_ne_y : s ≠ y :=
    Ne.symm fresh_y_ne_s
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_y_ne_a : y ≠ a := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_ne_s : x ≠ s := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_s_ne_x : s ≠ x :=
    Ne.symm fresh_x_ne_s
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_ne_s : z ≠ s := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_s_ne_z : s ≠ z :=
    Ne.symm fresh_z_ne_s
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_r_ne_z : r ≠ z :=
    Ne.symm fresh_z_ne_r
  have fresh_z_ne_a : z ≠ a := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have dv_cache_0001 : s ∉ (G).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : s ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ≠ s := by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ s from (by exact dv_a_s))
  have dv_cache_0004 : r ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ s from (by exact dv_r_s))
  have dv_cache_0005 : s ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_wf1o (.cv r) (.cv a) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_b, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wf1o (.cv r) (.cv a) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wf1o (.cv r) (.cv a) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_ccnv W)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_ccnv W)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((syn_ccnv W)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0014 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_enmap2lem3 (.cv y) (.cv x) G W s r a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_enmap2lem4_1
  have p0001 :=
    @g_enmap2lem3 (.cv z) (.cv x) G W s r a b dv_cache_0001 dv_cache_0005 dv_cache_0003 dv_cache_0004 hyp_enmap2lem4_1
  have p0002 :=
    @g_anim12d (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wbr (.cv y) W (.cv x)) (.classEq (.cv y) (syn_ccom (.cv x) (.cv r))) (syn_wbr (.cv z) W (.cv x)) (.classEq (.cv z) (syn_ccom (.cv x) (.cv r))) p0000 p0001
  have p0003 :=
    @g_eqtr3 (.cv y) (.cv z) (syn_ccom (.cv x) (.cv r))
  have p0004_e01_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv y) (syn_ccom (.cv x) (.cv r))) (.classEq (.cv z) (syn_ccom (.cv x) (.cv r)))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_ccom syn_copab syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0003
  have p0004 :=
    @g_syl6 (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (syn_wa (.classEq (.cv y) (syn_ccom (.cv x) (.cv r))) (.classEq (.cv z) (syn_ccom (.cv x) (.cv r)))) (.objEq y z) p0002 p0004_e01_recanon
  have p0005 :=
    @g_alrimiv (syn_wf1o (.cv r) (.cv a) (.cv b)) (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z)) z dv_cache_0006 p0004
  have p0006 :=
    @g_alrimivv (syn_wf1o (.cv r) (.cv a) (.cv b)) (.all z (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z))) x y dv_cache_0007 dv_cache_0008 p0005
  have p0007 :=
    @g_dffun2 x y z (syn_ccnv W) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0008 :=
    @g_brcnv (.cv x) (.cv y) W
  have p0009 :=
    @g_brcnv (.cv x) (.cv z) W
  have p0010 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_ccnv W) (.cv y)) (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv x) (syn_ccnv W) (.cv z)) (syn_wbr (.cv z) W (.cv x)) p0008 p0009
  have p0011 :=
    @g_imbi1i (syn_wa (syn_wbr (.cv x) (syn_ccnv W) (.cv y)) (syn_wbr (.cv x) (syn_ccnv W) (.cv z))) (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z) p0010
  have p0012 :=
    @g_albii (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv W) (.cv y)) (syn_wbr (.cv x) (syn_ccnv W) (.cv z))) (.objEq y z)) (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z)) z p0011
  have p0013 :=
    @g_n_2albii (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv W) (.cv y)) (syn_wbr (.cv x) (syn_ccnv W) (.cv z))) (.objEq y z))) (.all z (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z))) x y p0012
  have p0014 :=
    @g_bitri (syn_wfun (syn_ccnv W)) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv W) (.cv y)) (syn_wbr (.cv x) (syn_ccnv W) (.cv z))) (.objEq y z))))) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z))))) p0007 p0013
  have p0015 :=
    @g_sylibr (syn_wf1o (.cv r) (.cv a) (.cv b)) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z))))) (syn_wfun (syn_ccnv W)) p0006 p0014
  exact p0015

#print axioms g_enmap2lem4

end NFChoice.DirectNominalPrf.WPPReplay
