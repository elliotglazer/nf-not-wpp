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
import NominalWPPReplayChunk016Compact001Part070

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

noncomputable def g_hnsicodemapkernelndv
    (A : Class) (r : Var) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_q_r : q ≠ r) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wb (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))))) := by
  let proofSupport : Finset Var := A.fv ∪ ({r} : Finset Var) ∪ ({q} : Finset Var)
  let g : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_g_ne_r : g ≠ r := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_r_ne_g : r ≠ g :=
    Ne.symm fresh_g_ne_r
  have fresh_g_ne_q : g ≠ q := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_g : q ≠ g :=
    Ne.symm fresh_g_ne_q
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_f_ne_r : f ≠ r := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_r_ne_f : r ≠ f :=
    Ne.symm fresh_f_ne_r
  have fresh_f_ne_q : f ≠ q := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_f : q ≠ f :=
    Ne.symm fresh_f_ne_q
  have fresh_g_ne_f : g ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_g : f ≠ g :=
    Ne.symm fresh_g_ne_f
  have dv_cache_0001 : q ∉ ((syn_chwcn A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ r from (by exact dv_q_r))
  have dv_cache_0006 : f ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : f ∉ ((syn_cuni (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : f ∉ ((syn_cuni (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : f ∉ ((syn_cfv (syn_c2nd) (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : g ∉ ((syn_cfv (syn_c2nd) (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : f ∉ ((syn_cfv (syn_c2nd) (syn_cuni (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : g ∉ ((syn_cfv (syn_c2nd) (syn_cuni (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : f ∉ ((syn_cfv (syn_c1st) (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : g ∉ ((syn_cfv (syn_c1st) (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : f ∉ ((syn_cfv (syn_c1st) (syn_cuni (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : g ∉ ((syn_cfv (syn_c1st) (syn_cuni (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : f ≠ g := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show f ≠ g from (by exact fresh_f_ne_g))
  have dv_cache_0018 : g ∉ ((syn_cpw1 A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : g ∉ ((syn_cfv (syn_chnsicodemap A) (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_q, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : g ∉ ((syn_cfv (syn_chnsicodemap A) (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_r, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : r ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : g ∉ ((syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_q, fresh_g_not_A, fresh_g_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pw1typedbrndv (syn_chwcn A) (syn_chwniso A) r q dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0002 :=
    @g_hnwpw1argcl (syn_chwcn A) q
  have p0003 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0001 p0002
  have p0004 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0005 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) p0003 p0004
  have p0006 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0007 :=
    @g_hnwpw1argcl (syn_chwcn A) r
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) p0006 p0007
  have p0009 :=
    @g_simpl (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0008 p0009
  have p0011 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0005 p0010
  have p0012 :=
    @g_hwnisodirectisobclndv A (syn_cuni (.cv q)) (syn_cuni (.cv r)) f dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classMem (syn_cuni (.cv r)) (syn_chwcn A))) (syn_wb (syn_wbr (syn_cuni (.cv q)) (syn_chwniso A) (syn_cuni (.cv r))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0011 p0012
  have p0014 :=
    @g_pw1isoexequivndv (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv r))) f g (syn_cfv (syn_c2nd) (syn_cuni (.cv r))) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0015 :=
    @g_a1i (syn_wb (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) p0014
  have p0016 :=
    @g_bitrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wbr (syn_cuni (.cv q)) (syn_chwniso A) (syn_cuni (.cv r))) (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0013 p0015
  have p0017 :=
    @g_bitrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cuni (.cv q)) (syn_chwniso A) (syn_cuni (.cv r))) (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0000 p0016
  have p0018 :=
    @g_hnsicodemapfndv A
  have p0019 :=
    @g_a1i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) p0018
  have p0020 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0021 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0019 p0020
  have p0022 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (.cv q) (syn_chnsicodemap A)
  have p0023 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))) (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A))) p0021 p0022
  have p0024 :=
    @g_hnsicodemapfndv A
  have p0025 :=
    @g_a1i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) p0024
  have p0026 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0027 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0025 p0026
  have p0028 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (.cv r) (syn_chnsicodemap A)
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwcn (syn_cpw1 A))) p0027 p0028
  have p0030 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwcn (syn_cpw1 A))) p0023 p0029
  have p0031 :=
    @g_hwnisodirectisobclndv (syn_cpw1 A) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)) g dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0032 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wa (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwcn (syn_cpw1 A)))) (syn_wb (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))))) p0030 p0031
  have p0033 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0034 :=
    @g_hnsicodemapvalndv A q dv_cache_0021
  have p0035 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) p0033 p0034
  have p0036 :=
    @g_fveq2d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_c1st) p0035
  have p0037 :=
    @g_fvex (syn_cuni (.cv q)) (syn_c1st)
  have p0038 :=
    @g_siex (syn_cfv (syn_c1st) (syn_cuni (.cv q))) p0037
  have p0039 :=
    @g_fvex (syn_cuni (.cv q)) (syn_c2nd)
  have p0040 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0039
  have p0041 :=
    @g_opfv1st (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0038 p0040
  have p0042 :=
    @g_a1i (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) p0041
  have p0043 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) p0036 p0042
  have p0044 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (.cv g)
  have p0045 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))) (syn_wb (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))) p0043 p0044
  have p0046 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0047 :=
    @g_hnsicodemapvalndv A r dv_cache_0022
  have p0048 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0046 p0047
  have p0049 :=
    @g_fveq2d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) (syn_c1st) p0048
  have p0050 :=
    @g_fvex (syn_cuni (.cv r)) (syn_c1st)
  have p0051 :=
    @g_siex (syn_cfv (syn_c1st) (syn_cuni (.cv r))) p0050
  have p0052 :=
    @g_fvex (syn_cuni (.cv r)) (syn_c2nd)
  have p0053 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (.cv r))) p0052
  have p0054 :=
    @g_opfv1st (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) p0051 p0053
  have p0055 :=
    @g_a1i (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) p0054
  have p0056 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) p0049 p0055
  have p0057 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (.cv g)
  have p0058 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (syn_wb (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))) p0056 p0057
  have p0059 :=
    @g_bitrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) p0045 p0058
  have p0060 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0061 :=
    @g_hnsicodemapvalndv A q dv_cache_0021
  have p0062 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) p0060 p0061
  have p0063 :=
    @g_fveq2d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_c2nd) p0062
  have p0064 :=
    @g_fvex (syn_cuni (.cv q)) (syn_c1st)
  have p0065 :=
    @g_siex (syn_cfv (syn_c1st) (syn_cuni (.cv q))) p0064
  have p0066 :=
    @g_fvex (syn_cuni (.cv q)) (syn_c2nd)
  have p0067 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0066
  have p0068 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0065 p0067
  have p0069 :=
    @g_a1i (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) p0068
  have p0070 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0063 p0069
  have p0071 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (.cv g)
  have p0072 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_wb (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))) p0070 p0071
  have p0073 :=
    @g_bitrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) p0059 p0072
  have p0074 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0075 :=
    @g_hnsicodemapvalndv A r dv_cache_0022
  have p0076 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0074 p0075
  have p0077 :=
    @g_fveq2d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) (syn_c2nd) p0076
  have p0078 :=
    @g_fvex (syn_cuni (.cv r)) (syn_c1st)
  have p0079 :=
    @g_siex (syn_cfv (syn_c1st) (syn_cuni (.cv r))) p0078
  have p0080 :=
    @g_fvex (syn_cuni (.cv r)) (syn_c2nd)
  have p0081 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (.cv r))) p0080
  have p0082 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) p0079 p0081
  have p0083 :=
    @g_a1i (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) p0082
  have p0084 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) p0077 p0083
  have p0085 :=
    @g_isoeq5 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (.cv g)
  have p0086 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) (syn_wb (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0084 p0085
  have p0087 :=
    @g_bitrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) p0073 p0086
  have p0088 :=
    @g_exbidv (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) g dv_cache_0023 p0087
  have p0089 :=
    @g_bitrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0032 p0088
  have p0090 :=
    @g_bicomd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0089
  have p0091 :=
    @g_bitrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r)) (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))) p0017 p0090
  exact p0091

#print axioms g_hnsicodemapkernelndv

end NFChoice.DirectNominalPrf.WPPReplay
