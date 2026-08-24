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
import NominalWPPReplayChunk015Compact001Part003

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

noncomputable def g_lnqrelreps
    (v : Var) (u : Var) (C : Class) (R : Class) (X : Class) (Y : Class) (dv_C_u : u ∉ C.fv) (dv_C_v : v ∉ C.fv) (dv_R_u : u ∉ R.fv) (dv_R_v : v ∉ R.fv) (dv_X_u : u ∉ X.fv) (dv_X_v : v ∉ X.fv) (dv_Y_u : u ∉ Y.fv) (dv_Y_v : v ∉ Y.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wb (syn_wrex u (syn_cec X (syn_clnker R)) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v)))) (syn_wbr X R Y))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ C.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  have dv_cache_0001 : v ∉ ((syn_cec X (syn_clnker R))).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_v, dv_R_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_wbr X R Y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_u, dv_Y_u, dv_R_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((syn_wbr X R Y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_v, dv_Y_v, dv_R_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_u, dv_C_u, dv_X_u, dv_Y_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ∉ ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_v, dv_C_v, dv_X_v, dv_Y_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0007 : v ∉ (Y).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_Y_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : v ∉ ((syn_cec Y (syn_clnker R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_Y_v, dv_R_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : v ∉ ((Wff.classEq (.cv u) X)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_v), dv_X_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((syn_cec X (syn_clnker R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_u, dv_R_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_Y_u, dv_R_u, dv_X_u, dv_u_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0001 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0002 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0003 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0002
  have p0004 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0003
  have p0005 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_ctrans) C) p0001 p0004
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr R (syn_ctrans) C) p0000 p0005
  have p0007 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0008 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0009 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0010 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0009
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) p0008 p0010
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem X C) p0007 p0011
  have p0013 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0014 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0015 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0014
  have p0016 :=
    @g_ellnkerec v R Y
  have p0017 :=
    @g_biimpi (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0016
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0015 p0017
  have p0019 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y) p0018
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0021 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0022 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wss R (syn_cxp C C)) p0020 p0022
  have p0024 :=
    @g_ssbrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) R (syn_cxp C C) (.cv v) Y p0023
  have p0025 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv v) R Y) (syn_wbr (.cv v) (syn_cxp C C) Y) p0019 p0024
  have p0026 :=
    @g_brxp (.cv v) Y C C
  have p0027 :=
    @g_biimpi (syn_wbr (.cv v) (syn_cxp C C) Y) (syn_wa (.classMem (.cv v) C) (.classMem Y C)) p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv v) (syn_cxp C C) Y) (syn_wa (.classMem (.cv v) C) (.classMem Y C)) p0025 p0027
  have p0029 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) C) (.classMem Y C) p0028
  have p0030 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) C) p0013 p0029
  have p0031 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0032 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0033 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0034 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0033
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem Y C) p0032 p0034
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem Y C) p0031 p0035
  have p0037 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0038 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0039 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0040 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0039
  have p0041 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0040
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_ctrans) C) p0038 p0041
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr R (syn_ctrans) C) p0037 p0042
  have p0044 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0045 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0046 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0047 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0046
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) p0045 p0047
  have p0049 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem X C) p0044 p0048
  have p0050 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0051 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0052 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0051
  have p0053 :=
    @g_ellnkerec u R X
  have p0054 :=
    @g_biimpi (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0053
  have p0055 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0052 p0054
  have p0056 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X) p0055
  have p0057 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0058 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0059 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0058
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wss R (syn_cxp C C)) p0057 p0059
  have p0061 :=
    @g_ssbrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) R (syn_cxp C C) X (.cv u) p0060
  have p0062 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R (.cv u)) (syn_wbr X (syn_cxp C C) (.cv u)) p0056 p0061
  have p0063 :=
    @g_brxp X (.cv u) C C
  have p0064 :=
    @g_biimpi (syn_wbr X (syn_cxp C C) (.cv u)) (syn_wa (.classMem X C) (.classMem (.cv u) C)) p0063
  have p0065 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X (syn_cxp C C) (.cv u)) (syn_wa (.classMem X C) (.classMem (.cv u) C)) p0062 p0064
  have p0066 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem X C) (.classMem (.cv u) C) p0065
  have p0067 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) C) p0050 p0066
  have p0068 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0069 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0070 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0069
  have p0071 :=
    @g_ellnkerec v R Y
  have p0072 :=
    @g_biimpi (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0071
  have p0073 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0070 p0072
  have p0074 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y) p0073
  have p0075 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0076 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0077 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0076
  have p0078 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wss R (syn_cxp C C)) p0075 p0077
  have p0079 :=
    @g_ssbrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) R (syn_cxp C C) (.cv v) Y p0078
  have p0080 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv v) R Y) (syn_wbr (.cv v) (syn_cxp C C) Y) p0074 p0079
  have p0081 :=
    @g_brxp (.cv v) Y C C
  have p0082 :=
    @g_biimpi (syn_wbr (.cv v) (syn_cxp C C) Y) (syn_wa (.classMem (.cv v) C) (.classMem Y C)) p0081
  have p0083 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv v) (syn_cxp C C) Y) (syn_wa (.classMem (.cv v) C) (.classMem Y C)) p0080 p0082
  have p0084 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) C) (.classMem Y C) p0083
  have p0085 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) C) p0068 p0084
  have p0086 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0087 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0088 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0087
  have p0089 :=
    @g_ellnkerec u R X
  have p0090 :=
    @g_biimpi (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0089
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0088 p0090
  have p0092 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X) p0091
  have p0093 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R (.cv u)) p0086 p0092
  have p0094 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0095 :=
    @g_trd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) C R X (.cv u) (.cv v) p0043 p0049 p0067 p0085 p0093 p0094
  have p0096 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))
  have p0097 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0098 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0097
  have p0099 :=
    @g_ellnkerec v R Y
  have p0100 :=
    @g_biimpi (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0099
  have p0101 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0098 p0100
  have p0102 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y) p0101
  have p0103 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv v) R Y) p0096 p0102
  have p0104 :=
    @g_trd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v))) C R X (.cv v) Y p0006 p0012 p0030 p0036 p0095 p0103
  have p0105 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R Y) p0104
  have p0106 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0107 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0108 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0109 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0108
  have p0110 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0109
  have p0111 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_ctrans) C) p0107 p0110
  have p0112 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr R (syn_ctrans) C) p0106 p0111
  have p0113 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0114 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0115 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0114
  have p0116 :=
    @g_ellnkerec u R X
  have p0117 :=
    @g_biimpi (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0116
  have p0118 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0115 p0117
  have p0119 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X) p0118
  have p0120 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0121 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0122 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0121
  have p0123 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wss R (syn_cxp C C)) p0120 p0122
  have p0124 :=
    @g_ssbrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) R (syn_cxp C C) X (.cv u) p0123
  have p0125 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R (.cv u)) (syn_wbr X (syn_cxp C C) (.cv u)) p0119 p0124
  have p0126 :=
    @g_brxp X (.cv u) C C
  have p0127 :=
    @g_biimpi (syn_wbr X (syn_cxp C C) (.cv u)) (syn_wa (.classMem X C) (.classMem (.cv u) C)) p0126
  have p0128 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X (syn_cxp C C) (.cv u)) (syn_wa (.classMem X C) (.classMem (.cv u) C)) p0125 p0127
  have p0129 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem X C) (.classMem (.cv u) C) p0128
  have p0130 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) C) p0113 p0129
  have p0131 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0132 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0133 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0134 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0133
  have p0135 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem Y C) p0132 p0134
  have p0136 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem Y C) p0131 p0135
  have p0137 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0138 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0139 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0138
  have p0140 :=
    @g_ellnkerec v R Y
  have p0141 :=
    @g_biimpi (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0140
  have p0142 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0139 p0141
  have p0143 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y) p0142
  have p0144 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0145 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0146 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0145
  have p0147 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wss R (syn_cxp C C)) p0144 p0146
  have p0148 :=
    @g_ssbrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) R (syn_cxp C C) (.cv v) Y p0147
  have p0149 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv v) R Y) (syn_wbr (.cv v) (syn_cxp C C) Y) p0143 p0148
  have p0150 :=
    @g_brxp (.cv v) Y C C
  have p0151 :=
    @g_biimpi (syn_wbr (.cv v) (syn_cxp C C) Y) (syn_wa (.classMem (.cv v) C) (.classMem Y C)) p0150
  have p0152 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv v) (syn_cxp C C) Y) (syn_wa (.classMem (.cv v) C) (.classMem Y C)) p0149 p0151
  have p0153 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) C) (.classMem Y C) p0152
  have p0154 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) C) p0137 p0153
  have p0155 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0156 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0157 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0158 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0157
  have p0159 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0158
  have p0160 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_ctrans) C) p0156 p0159
  have p0161 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr R (syn_ctrans) C) p0155 p0160
  have p0162 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0163 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0164 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0163
  have p0165 :=
    @g_ellnkerec u R X
  have p0166 :=
    @g_biimpi (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0165
  have p0167 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0164 p0166
  have p0168 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X) p0167
  have p0169 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0170 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0171 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0170
  have p0172 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wss R (syn_cxp C C)) p0169 p0171
  have p0173 :=
    @g_ssbrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) R (syn_cxp C C) X (.cv u) p0172
  have p0174 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R (.cv u)) (syn_wbr X (syn_cxp C C) (.cv u)) p0168 p0173
  have p0175 :=
    @g_brxp X (.cv u) C C
  have p0176 :=
    @g_biimpi (syn_wbr X (syn_cxp C C) (.cv u)) (syn_wa (.classMem X C) (.classMem (.cv u) C)) p0175
  have p0177 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X (syn_cxp C C) (.cv u)) (syn_wa (.classMem X C) (.classMem (.cv u) C)) p0174 p0176
  have p0178 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem X C) (.classMem (.cv u) C) p0177
  have p0179 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) C) p0162 p0178
  have p0180 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0181 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0182 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0183 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0182
  have p0184 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) p0181 p0183
  have p0185 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem X C) p0180 p0184
  have p0186 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0187 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0188 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0189 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0188
  have p0190 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem Y C) p0187 p0189
  have p0191 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem Y C) p0186 p0190
  have p0192 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0193 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0194 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0193
  have p0195 :=
    @g_ellnkerec u R X
  have p0196 :=
    @g_biimpi (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0195
  have p0197 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0194 p0196
  have p0198 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X) p0197
  have p0199 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R X) p0192 p0198
  have p0200 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0201 :=
    @g_trd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) C R (.cv u) X Y p0161 p0179 p0185 p0191 p0199 p0200
  have p0202 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)
  have p0203 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))
  have p0204 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) p0203
  have p0205 :=
    @g_ellnkerec v R Y
  have p0206 :=
    @g_biimpi (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0205
  have p0207 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y)) p0204 p0206
  have p0208 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr Y R (.cv v)) (syn_wbr (.cv v) R Y) p0207
  have p0209 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr Y R (.cv v)) p0202 p0208
  have p0210 :=
    @g_trd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y)) C R (.cv u) Y (.cv v) p0112 p0130 p0136 p0154 p0201 p0209
  have p0211 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr X R Y) (syn_wbr (.cv u) R (.cv v)) p0210
  have p0212 :=
    @g_impbid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R Y) p0105 p0211
  have p0213 :=
    @g_biimpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (.cv u) (syn_cec X (syn_clnker R))) (.classMem (.cv v) (syn_cec Y (syn_clnker R))))) (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R Y) p0212
  have p0214 :=
    @g_rexlimdvva (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R Y) u v (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0213
  have p0215 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y)
  have p0216 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0217 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0216
  have p0218 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0217
  have p0219 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0220 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0219
  have p0221 :=
    @g_refd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) C R X p0218 p0220
  have p0222 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0223 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0222
  have p0224 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0223
  have p0225 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0226 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0225
  have p0227 :=
    @g_refd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) C R X p0224 p0226
  have p0228 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R X) (syn_wbr X R X) p0221 p0227
  have p0229 :=
    @g_elec X X (syn_clnker R)
  have p0230 :=
    @g_brlnker R X X
  have p0231 :=
    @g_bitri (.classMem X (syn_cec X (syn_clnker R))) (syn_wbr X (syn_clnker R) X) (syn_wa (syn_wbr X R X) (syn_wbr X R X)) p0229 p0230
  have p0232 :=
    @g_biimpri (.classMem X (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R X) (syn_wbr X R X)) p0231
  have p0233 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R X) (syn_wbr X R X)) (.classMem X (syn_cec X (syn_clnker R))) p0228 p0232
  have p0234 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X (syn_cec X (syn_clnker R))) p0215 p0233
  have p0235 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y)
  have p0236 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0237 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0236
  have p0238 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0237
  have p0239 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0240 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0239
  have p0241 :=
    @g_refd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) C R Y p0238 p0240
  have p0242 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0243 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0242
  have p0244 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C) p0243
  have p0245 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0246 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem X C) (.classMem Y C) p0245
  have p0247 :=
    @g_refd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) C R Y p0244 p0246
  have p0248 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr Y R Y) (syn_wbr Y R Y) p0241 p0247
  have p0249 :=
    @g_elec Y Y (syn_clnker R)
  have p0250 :=
    @g_brlnker R Y Y
  have p0251 :=
    @g_bitri (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wbr Y (syn_clnker R) Y) (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y)) p0249 p0250
  have p0252 :=
    @g_biimpri (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y)) p0251
  have p0253 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y)) (.classMem Y (syn_cec Y (syn_clnker R))) p0248 p0252
  have p0254 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem Y (syn_cec Y (syn_clnker R))) p0235 p0253
  have p0255 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y)
  have p0256 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y)) (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wbr X R Y) p0254 p0255
  have p0257 :=
    @g_breq2 (.cv v) Y X R
  have p0258 :=
    @g_rspcev (syn_wbr X R (.cv v)) (syn_wbr X R Y) v Y (syn_cec Y (syn_clnker R)) dv_cache_0007 dv_cache_0008 dv_cache_0003 p0257
  have p0259 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y)) (syn_wa (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wbr X R Y)) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v))) p0256 p0258
  have p0260 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y)) (.classMem X (syn_cec X (syn_clnker R))) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v))) p0234 p0259
  have p0261 :=
    @g_breq1 (.cv u) X (.cv v) R
  have p0262 :=
    @g_rexbidv (.classEq (.cv u) X) (syn_wbr (.cv u) R (.cv v)) (syn_wbr X R (.cv v)) v (syn_cec Y (syn_clnker R)) dv_cache_0009 p0261
  have p0263 :=
    @g_rspcev (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v))) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v))) u X (syn_cec X (syn_clnker R)) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0262
  have p0264 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y)) (syn_wa (.classMem X (syn_cec X (syn_clnker R))) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr X R (.cv v)))) (syn_wrex u (syn_cec X (syn_clnker R)) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v)))) p0260 p0263
  have p0265 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr X R Y) (syn_wrex u (syn_cec X (syn_clnker R)) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v)))) p0264
  have p0266 :=
    @g_impbid (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wrex u (syn_cec X (syn_clnker R)) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v)))) (syn_wbr X R Y) p0214 p0265
  exact p0266

#print axioms g_lnqrelreps

end NFChoice.DirectNominalPrf.WPPReplay
