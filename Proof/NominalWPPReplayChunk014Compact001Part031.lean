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
import NominalWPPReplayChunk014Compact001Part030

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

noncomputable def g_hwisotri
    (w : Var) (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) (dv_u_v : u ≠ v) (dv_u_w : u ≠ w) (dv_v_w : v ≠ w) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w))) := by
  let proofSupport : Finset Var := ({w} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  let h : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  let g : Var := freshVar proofSupport 2
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_w : h ≠ w := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_h : w ≠ h :=
    Ne.symm fresh_h_ne_w
  have fresh_h_ne_v : h ≠ v := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_h : v ≠ h :=
    Ne.symm fresh_h_ne_v
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_h : u ≠ h :=
    Ne.symm fresh_h_ne_u
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_ne_w : f ≠ w := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_f : w ≠ f :=
    Ne.symm fresh_f_ne_w
  have fresh_f_ne_v : f ≠ v := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_f : v ≠ f :=
    Ne.symm fresh_f_ne_v
  have fresh_f_ne_u : f ≠ u := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_f : u ≠ f :=
    Ne.symm fresh_f_ne_u
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_g_ne_w : g ≠ w := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_g : w ≠ g :=
    Ne.symm fresh_g_ne_w
  have fresh_g_ne_v : g ≠ v := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_g : v ≠ g :=
    Ne.symm fresh_g_ne_v
  have fresh_g_ne_u : g ≠ u := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_g : u ≠ g :=
    Ne.symm fresh_g_ne_u
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_h_ne_f : h ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_h : f ≠ h :=
    Ne.symm fresh_h_ne_f
  have fresh_h_ne_g : h ≠ g := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_g_ne_h : g ≠ h :=
    Ne.symm fresh_h_ne_g
  have fresh_f_ne_g : f ≠ g := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_g_ne_f : g ≠ f :=
    Ne.symm fresh_f_ne_g
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0005 : f ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact fresh_f_ne_v))
  have dv_cache_0006 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0007 : g ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : g ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show g ≠ v from (by exact fresh_g_ne_v))
  have dv_cache_0010 : g ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show g ≠ w from (by exact fresh_g_ne_w))
  have dv_cache_0011 : v ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show v ≠ w from (by exact dv_v_w))
  have dv_cache_0012 : g ∉ ((syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_u, fresh_g_ne_v, fresh_g_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : f ∉ ((syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_v, fresh_f_ne_w, fresh_f_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : h ∉ ((syn_ccom (.cv g) (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_g, fresh_h_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : h ∉ ((syn_wiso (syn_ccom (.cv g) (.cv f)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_u, fresh_h_ne_w, fresh_h_ne_g, fresh_h_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : f ∉ ((syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_u, fresh_f_ne_w, fresh_f_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : g ∉ ((syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_u, fresh_g_ne_w, fresh_g_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : h ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0020 : h ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show h ≠ w from (by exact fresh_h_ne_w))
  have dv_cache_0021 : u ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show u ≠ w from (by exact dv_u_w))
  have p0000 :=
    @g_brhwiso v u A f dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0000
  have p0002 :=
    @g_brhwiso w v A g dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0003 :=
    @g_biimpi (syn_wbr (.cv v) (syn_chwiso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))) p0002
  have p0004 :=
    @g_anim12i (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))) p0001 p0003
  have p0005 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
  have p0006 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0007 :=
    @g_simpl (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))
  have p0008 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (.classMem (.cv u) (syn_chwcodes A)) p0006 p0007
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (.cv u) (syn_chwcodes A)) p0005 p0008
  have p0010 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
  have p0011 :=
    @g_simpl (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))
  have p0012 :=
    @g_simpr (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))) (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (.classMem (.cv w) (syn_chwcodes A)) p0011 p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))) (.classMem (.cv w) (syn_chwcodes A)) p0010 p0013
  have p0015 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)) p0009 p0014
  have p0016 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
  have p0017 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0016 p0017
  have p0019 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
  have p0020 :=
    @g_simpr (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))) p0019 p0020
  have p0022 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))) p0018 p0021
  have p0023 :=
    @g_eeanv (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))) f g dv_cache_0012 dv_cache_0013
  have p0024 :=
    @g_biimpri (syn_wex f (syn_wex g (syn_wa (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wa (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))) p0023
  have p0025 :=
    @g_isotr (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (.cv g) (.cv f)
  have p0026 :=
    @g_vex g
  have p0027 :=
    @g_vex f
  have p0028 :=
    @g_coex (.cv g) (.cv f) p0026 p0027
  have p0029 :=
    @g_isoeq1 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_ccom (.cv g) (.cv f)) (.cv h)
  have p0030 :=
    @g_spcev (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))) (syn_wiso (syn_ccom (.cv g) (.cv f)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))) h (syn_ccom (.cv g) (.cv f)) dv_cache_0014 dv_cache_0015 p0028 p0029
  have p0031 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))) (syn_wiso (syn_ccom (.cv g) (.cv f)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))) p0025 p0030
  have p0032 :=
    @g_exlimivv (syn_wa (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))) f g dv_cache_0016 dv_cache_0017 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))) (syn_wex f (syn_wex g (syn_wa (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))) p0024 p0032
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wa (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))) p0022 p0033
  have p0035 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))) p0015 p0034
  have p0036 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))) p0004 p0035
  have p0037 :=
    @g_brhwiso w u A h dv_cache_0018 dv_cache_0002 dv_cache_0008 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0038 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))) p0037
  have p0039 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0036 p0038
  exact p0039

noncomputable def g_hwisorefl
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcodes A)) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_u_ne_h : u ≠ h :=
    Ne.symm fresh_h_ne_u
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : h ∉ ((syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((syn_wiso (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have p0000 :=
    @g_pm4_24 (.classMem (.cv u) (syn_chwcodes A))
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcodes A)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) p0000
  have p0002 :=
    @g_isoid (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0003 :=
    @g_idex
  have p0004 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0005 :=
    @g_resex (syn_cid) (syn_cfv (syn_c2nd) (.cv u)) p0003 p0004
  have p0006 :=
    @g_isoeq1 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u))) (.cv h)
  have p0007 :=
    @g_spcev (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_wiso (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) h (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u))) dv_cache_0001 dv_cache_0002 p0005 p0006
  have p0008 :=
    Nominal.mp p0002 p0007
  have p0009 :=
    @g_a1i (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcodes A)) p0008
  have p0010 :=
    @g_jca (.classMem (.cv u) (syn_chwcodes A)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0001 p0009
  have p0011 :=
    @g_brhwisoany u u A h dv_cache_0003 dv_cache_0004 dv_cache_0004
  have p0012 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0011
  have p0013 :=
    @g_syl (.classMem (.cv u) (syn_chwcodes A)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0010 p0012
  exact p0013

noncomputable def g_hwrelsex
     :
    Nominal.NPrf (.classMem (syn_chwrels) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_chwrels] using (Nominal.classEqRefl (syn_chwrels)))
  have p0001 :=
    @g_n_1stex
  have p0002 :=
    @g_crossex
  have p0003 :=
    @g_n_2ndex
  have p0004 :=
    @g_n_2ndex
  have p0005 :=
    @g_txpex (syn_c2nd) (syn_c2nd) p0003 p0004
  have p0006 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0002 p0005
  have p0007 :=
    @g_txpex (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) p0001 p0006
  have p0008 :=
    @g_cnvex (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0007
  have p0009 :=
    @g_ssetex
  have p0010 :=
    @g_imaex (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset) p0008 p0009
  have p0011 :=
    @g_eqeltri (syn_chwrels) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)) (syn_cvv) p0000 p0010
  exact p0011

noncomputable def g_hwbijex
     :
    Nominal.NPrf (.classMem (syn_chwbij) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_chwbij] using (Nominal.classEqRefl (syn_chwbij)))
  have p0001 :=
    @g_funsex
  have p0002 :=
    @g_swapex
  have p0003 :=
    @g_imageex (syn_cswap) p0002
  have p0004 :=
    @g_cnvex (syn_cimage (syn_cswap)) p0003
  have p0005 :=
    @g_funsex
  have p0006 :=
    @g_imaex (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns) p0004 p0005
  have p0007 :=
    @g_inex (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)) p0001 p0006
  have p0008 :=
    @g_eqeltri (syn_chwbij) (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))) (syn_cvv) p0000 p0007
  exact p0008

noncomputable def g_hwgenex
     :
    Nominal.NPrf (.classMem (syn_chwgen) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_chwgen] using (Nominal.classEqRefl (syn_chwgen)))
  have p0001 :=
    @g_n_2ndex
  have p0002 :=
    @g_domfnex
  have p0003 :=
    @g_n_1stex
  have p0004 :=
    @g_coex (syn_cdomfn) (syn_c1st) p0002 p0003
  have p0005 :=
    @g_txpex (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)) p0001 p0004
  have p0006 :=
    (by simpa [syn_chwtrn] using (Nominal.classEqRefl (syn_chwtrn)))
  have p0007 :=
    @g_composeex
  have p0008 :=
    @g_composeex
  have p0009 :=
    @g_n_1stex
  have p0010 :=
    @g_n_2ndex
  have p0011 :=
    @g_txpex (syn_c1st) (syn_c2nd) p0009 p0010
  have p0012 :=
    @g_coex (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)) p0008 p0011
  have p0013 :=
    @g_swapex
  have p0014 :=
    @g_imageex (syn_cswap) p0013
  have p0015 :=
    @g_n_1stex
  have p0016 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_c1st) p0014 p0015
  have p0017 :=
    @g_txpex (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) p0012 p0016
  have p0018 :=
    @g_coex (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0007 p0017
  have p0019 :=
    @g_eqeltri (syn_chwtrn) (syn_ccom (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv) p0006 p0018
  have p0020 :=
    @g_ranfnex
  have p0021 :=
    @g_n_1stex
  have p0022 :=
    @g_coex (syn_cranfn) (syn_c1st) p0020 p0021
  have p0023 :=
    @g_txpex (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)) p0019 p0022
  have p0024 :=
    @g_txpex (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) p0005 p0023
  have p0025 :=
    @g_eqeltri (syn_chwgen) (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cvv) p0000 p0024
  exact p0025

noncomputable def g_hwcnex
    (A : Class) (hyp_hwcnex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_chwcn A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0001 :=
    @g_hwcodesex A hyp_hwcnex_1
  have p0002 :=
    (by simpa [syn_chwrels] using (Nominal.classEqRefl (syn_chwrels)))
  have p0003 :=
    @g_n_1stex
  have p0004 :=
    @g_crossex
  have p0005 :=
    @g_n_2ndex
  have p0006 :=
    @g_n_2ndex
  have p0007 :=
    @g_txpex (syn_c2nd) (syn_c2nd) p0005 p0006
  have p0008 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0004 p0007
  have p0009 :=
    @g_txpex (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) p0003 p0008
  have p0010 :=
    @g_cnvex (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0009
  have p0011 :=
    @g_ssetex
  have p0012 :=
    @g_imaex (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset) p0010 p0011
  have p0013 :=
    @g_eqeltri (syn_chwrels) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)) (syn_cvv) p0002 p0012
  have p0014 :=
    @g_inex (syn_chwcodes A) (syn_chwrels) p0001 p0013
  have p0015 :=
    @g_eqeltri (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv) p0000 p0014
  exact p0015

noncomputable def g_hwnisoex
    (A : Class) (hyp_hwnisoex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_chwniso A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chwniso] using (Nominal.classEqRefl (syn_chwniso A)))
  have p0001 :=
    @g_hwgenex
  have p0002 :=
    @g_hwbijex
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0002 p0003
  have p0005 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_hwcnex A hyp_hwnisoex_1
  have p0007 :=
    @g_hwcnex A hyp_hwnisoex_1
  have p0008 :=
    @g_xpex (syn_chwcn A) (syn_chwcn A) p0006 p0007
  have p0009 :=
    @g_inex (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0005 p0008
  have p0010 :=
    @g_eqeltri (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_cvv) p0000 p0009
  exact p0010

noncomputable def g_hnordex
    (A : Class) (hyp_hnordex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_chnord A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0001 :=
    @g_hwnisoex A hyp_hnordex_1
  have p0002 :=
    @g_hwcnex A hyp_hnordex_1
  have p0003 :=
    @g_qsex (syn_chwcn A) (syn_chwniso A) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv) p0000 p0003
  exact p0004

#print axioms g_hnordex

end NFChoice.DirectNominalPrf.WPPReplay
