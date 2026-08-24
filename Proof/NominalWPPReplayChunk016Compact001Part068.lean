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
import NominalWPPReplayChunk016Compact001Part067

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

noncomputable def g_pw1raiseisomdv
    (D : Class) (R : Class) (S : Class) (f : Var) (E : Class) :
    Nominal.NPrf (.imp (syn_wiso (.cv f) R S D E) (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ ({f} : Finset Var) ∪ E.fv
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_S : p ∉ S.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_ne_f : p ≠ f := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_p : f ≠ p :=
    Ne.symm fresh_p_ne_f
  have fresh_p_not_E : p ∉ E.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_not_S : q ∉ S.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_ne_f : q ≠ f := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_q : f ≠ q :=
    Ne.symm fresh_q_ne_f
  have fresh_q_not_E : q ∉ E.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0006 : q ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_wiso (.cv f) R S D E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, fresh_p_not_E, fresh_p_ne_f, fresh_p_not_R, fresh_p_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_wiso (.cv f) R S D E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, fresh_q_not_E, fresh_q_ne_f, fresh_q_not_R, fresh_q_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((syn_cpw1 E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : q ∉ ((syn_cpw1 E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_csi (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((syn_csi (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : q ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((syn_csi S)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : q ∉ ((syn_csi S)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_isof1o D E R S (.cv f)
  have p0001 :=
    @g_pw1sif1omapndv D E (.cv f)
  have p0002 :=
    @g_syl (syn_wiso (.cv f) R S D E) (syn_wf1o (.cv f) D E) (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 D) (syn_cpw1 E)) p0000 p0001
  have p0003 :=
    @g_simpr (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0004 :=
    @g_pw1typedbrndv D R q p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0005 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q)) (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q)))) p0003 p0004
  have p0006 :=
    @g_simpl (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0007 :=
    @g_simpr (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0008 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0009 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (.classMem (.cv p) (syn_cpw1 D)) p0007 p0008
  have p0010 :=
    @g_hnwpw1argcl D p
  have p0011 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (.classMem (.cv p) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0009 p0010
  have p0012 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0013 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classMem (syn_cuni (.cv p)) D) p0011 p0012
  have p0014 :=
    @g_simpr (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0015 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0016 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 D)) p0014 p0015
  have p0017 :=
    @g_hnwpw1argcl D q
  have p0018 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (.classMem (.cv q) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0016 p0017
  have p0019 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0020 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) D) p0018 p0019
  have p0021 :=
    @g_jca (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (.classMem (syn_cuni (.cv p)) D) (.classMem (syn_cuni (.cv q)) D) p0013 p0020
  have p0022 :=
    @g_jca (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classMem (syn_cuni (.cv q)) D)) p0006 p0021
  have p0023 :=
    @g_isorel D E (syn_cuni (.cv p)) (syn_cuni (.cv q)) R S (.cv f)
  have p0024 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classMem (syn_cuni (.cv q)) D))) (syn_wb (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q))) (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q))))) p0022 p0023
  have p0025 :=
    @g_bitrd (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wbr (.cv p) (syn_csi R) (.cv q)) (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q))) (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q)))) p0005 p0024
  have p0026 :=
    @g_simpr (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0027 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0028 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (.classMem (.cv p) (syn_cpw1 D)) p0026 p0027
  have p0029 :=
    @g_hnwpw1argcl D p
  have p0030 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (.classMem (.cv p) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0028 p0029
  have p0031 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0032 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0030 p0031
  have p0033 :=
    @g_fveq2d (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_csi (.cv f)) p0032
  have p0034 :=
    @g_simpl (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0035 :=
    @g_isof1o D E R S (.cv f)
  have p0036 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wiso (.cv f) R S D E) (syn_wf1o (.cv f) D E) p0034 p0035
  have p0037 :=
    @g_f1of D E (.cv f)
  have p0038 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wf1o (.cv f) D E) (syn_wf (.cv f) D E) p0036 p0037
  have p0039 :=
    @g_simpr (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0040 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0041 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (.classMem (.cv p) (syn_cpw1 D)) p0039 p0040
  have p0042 :=
    @g_hnwpw1argcl D p
  have p0043 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (.classMem (.cv p) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0041 p0042
  have p0044 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0045 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classMem (syn_cuni (.cv p)) D) p0043 p0044
  have p0046 :=
    @g_jca (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wf (.cv f) D E) (.classMem (syn_cuni (.cv p)) D) p0038 p0045
  have p0047 :=
    @g_sifvalimpclndv (syn_cuni (.cv p)) D E (.cv f)
  have p0048 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (syn_wf (.cv f) D E) (.classMem (syn_cuni (.cv p)) D)) (.classEq (syn_cfv (syn_csi (.cv f)) (syn_csn (syn_cuni (.cv p)))) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p))))) p0046 p0047
  have p0049 :=
    @g_eqtrd (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_cfv (syn_csi (.cv f)) (syn_csn (syn_cuni (.cv p)))) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p)))) p0033 p0048
  have p0050 :=
    @g_simpr (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0051 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0052 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 D)) p0050 p0051
  have p0053 :=
    @g_hnwpw1argcl D q
  have p0054 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (.classMem (.cv q) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0052 p0053
  have p0055 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0056 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0054 p0055
  have p0057 :=
    @g_fveq2d (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_csi (.cv f)) p0056
  have p0058 :=
    @g_simpl (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0059 :=
    @g_isof1o D E R S (.cv f)
  have p0060 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wiso (.cv f) R S D E) (syn_wf1o (.cv f) D E) p0058 p0059
  have p0061 :=
    @g_f1of D E (.cv f)
  have p0062 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wf1o (.cv f) D E) (syn_wf (.cv f) D E) p0060 p0061
  have p0063 :=
    @g_simpr (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0064 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0065 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 D)) p0063 p0064
  have p0066 :=
    @g_hnwpw1argcl D q
  have p0067 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (.classMem (.cv q) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0065 p0066
  have p0068 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0069 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) D) p0067 p0068
  have p0070 :=
    @g_jca (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wf (.cv f) D E) (.classMem (syn_cuni (.cv q)) D) p0062 p0069
  have p0071 :=
    @g_sifvalimpclndv (syn_cuni (.cv q)) D E (.cv f)
  have p0072 :=
    @g_syl (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wa (syn_wf (.cv f) D E) (.classMem (syn_cuni (.cv q)) D)) (.classEq (syn_cfv (syn_csi (.cv f)) (syn_csn (syn_cuni (.cv q)))) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q))))) p0070 p0071
  have p0073 :=
    @g_eqtrd (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_cfv (syn_csi (.cv f)) (.cv q)) (syn_cfv (syn_csi (.cv f)) (syn_csn (syn_cuni (.cv q)))) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q)))) p0057 p0072
  have p0074 :=
    @g_breq12d (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p)))) (syn_cfv (syn_csi (.cv f)) (.cv q)) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q)))) (syn_csi S) p0049 p0073
  have p0075 :=
    @g_fvex (syn_cuni (.cv p)) (.cv f)
  have p0076 :=
    @g_fvex (syn_cuni (.cv q)) (.cv f)
  have p0077 :=
    @g_brsnsi (syn_cfv (.cv f) (syn_cuni (.cv p))) (syn_cfv (.cv f) (syn_cuni (.cv q))) S p0075 p0076
  have p0078 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p)))) (syn_csi S) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q))))) (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q))))) (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) p0077
  have p0079 :=
    @g_bitrd (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S) (syn_cfv (syn_csi (.cv f)) (.cv q))) (syn_wbr (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p)))) (syn_csi S) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q))))) (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q)))) p0074 p0078
  have p0080 :=
    @g_bicomd (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S) (syn_cfv (syn_csi (.cv f)) (.cv q))) (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q)))) p0079
  have p0081 :=
    @g_bitrd (syn_wa (syn_wiso (.cv f) R S D E) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))) (syn_wbr (.cv p) (syn_csi R) (.cv q)) (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q)))) (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S) (syn_cfv (syn_csi (.cv f)) (.cv q))) p0025 p0080
  have p0082 :=
    @g_ralrimivva (syn_wiso (.cv f) R S D E) (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q)) (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S) (syn_cfv (syn_csi (.cv f)) (.cv q)))) p q (syn_cpw1 D) (syn_cpw1 D) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0005 p0081
  have p0083 :=
    @g_jca (syn_wiso (.cv f) R S D E) (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 D) (syn_cpw1 E)) (syn_wral p (syn_cpw1 D) (syn_wral q (syn_cpw1 D) (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q)) (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S) (syn_cfv (syn_csi (.cv f)) (.cv q)))))) p0002 p0082
  have p0084 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso p q (syn_cpw1 D) (syn_cpw1 E) (syn_csi R) (syn_csi S) (syn_csi (.cv f)) dv_cache_0009 dv_cache_0006 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0005
  have p0085 :=
    @g_biimpri (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 D) (syn_cpw1 E)) (syn_wral p (syn_cpw1 D) (syn_wral q (syn_cpw1 D) (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q)) (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S) (syn_cfv (syn_csi (.cv f)) (.cv q))))))) p0084
  have p0086 :=
    @g_syl (syn_wiso (.cv f) R S D E) (syn_wa (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 D) (syn_cpw1 E)) (syn_wral p (syn_cpw1 D) (syn_wral q (syn_cpw1 D) (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q)) (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S) (syn_cfv (syn_csi (.cv f)) (.cv q))))))) (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) p0083 p0085
  exact p0086

noncomputable def g_hndownbrndv
    (x : Var) (y : Var) (g : Var) (a : Var) (b : Var) (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_g_x : g ≠ x) (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({g} : Finset Var) ∪ ({a} : Finset Var) ∪ ({b} : Finset Var)
  have dv_cache_0001 : x ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_b_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_b_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_x), (Ne.symm dv_b_x), (Ne.symm dv_g_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_y), (Ne.symm dv_b_y), (Ne.symm dv_g_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_vex a
  have p0001 :=
    @g_vex b
  have p0002 :=
    @g_id (.classEq (.cv x) (.cv a))
  have p0003 :=
    @g_sneqd (.classEq (.cv x) (.cv a)) (.cv x) (.cv a) p0002
  have p0004 :=
    @g_breq1d (.classEq (.cv x) (.cv a)) (syn_csn (.cv x)) (syn_csn (.cv a)) (syn_csn (.cv y)) (.cv g) p0003
  have p0005 :=
    @g_id (.classEq (.cv y) (.cv b))
  have p0006 :=
    @g_sneqd (.classEq (.cv y) (.cv b)) (.cv y) (.cv b) p0005
  have p0007 :=
    @g_breq2d (.classEq (.cv y) (.cv b)) (syn_csn (.cv y)) (syn_csn (.cv b)) (syn_csn (.cv a)) (.cv g) p0006
  have p0008 :=
    @g_eqid (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
  have p0009 :=
    @g_brab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) x y (.cv a) (.cv b) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0001 p0004 p0007 p0008
  exact p0009

noncomputable def g_hndownexndv
    (x : Var) (y : Var) (g : Var) (dv_g_x : g ≠ x) (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({g} : Finset Var)
  have dv_cache_0001 : g ≠ x := by
    exact (show g ≠ x from (by exact dv_g_x))
  have dv_cache_0002 : g ≠ y := by
    clear dv_cache_0001
    exact (show g ≠ y from (by exact dv_g_y))
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_enpw1lem1 x y g dv_cache_0001 dv_cache_0002 dv_cache_0003
  exact p0000

#print axioms g_hndownexndv

end NFChoice.DirectNominalPrf.WPPReplay
