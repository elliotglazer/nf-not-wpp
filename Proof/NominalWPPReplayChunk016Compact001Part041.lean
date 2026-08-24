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
import NominalWPPReplayChunk016Compact001Part040

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

noncomputable def g_wppcandminfixedpivotpairdrfdv
    (z : Var) (C : Class) (D : Class) (R : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_R_n : n ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_n_z : n ≠ z) (hyp_wppcandminfixedpivotpairdrfdv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({n} : Finset Var) ∪ F.fv
  have dv_cache_0001 : z ∉ ((syn_cwppcand F C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, dv_R_z, dv_D_z, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_R_n, dv_D_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_R_n, dv_D_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_R_n, dv_D_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, dv_R_z, dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_n, dv_R_n, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, dv_R_z, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : n ∉ ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_n, dv_D_n, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, dv_D_z, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show n ≠ z from (by exact dv_n_z))
  have p0000 :=
    @g_biid (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
  have p0001 :=
    @g_a1i (syn_wb (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) p0000
  have p0002 :=
    @g_biid (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
  have p0003 :=
    @g_a1i (syn_wb (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) p0002
  have p0004 :=
    @g_id (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))
  have p0005 :=
    @g_sneqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) p0004
  have p0006 :=
    @g_imaeq2d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_csn C) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_ccnv (syn_clec)) p0005
  have p0007 :=
    @g_ineq2d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))) (syn_chwcards (syn_cvv)) p0006
  have p0008 :=
    @g_eqidd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cimage (syn_ccnv F))
  have p0009 :=
    @g_id (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))
  have p0010 :=
    @g_sneqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) p0009
  have p0011 :=
    @g_imaeq2d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_csn C) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_clec) p0010
  have p0012 :=
    @g_jca (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F))) (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))) p0008 p0011
  have p0013 :=
    @g_freceq12 (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))
  have p0014 :=
    @g_syl (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wa (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F))) (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))) (.classEq (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))) p0012 p0013
  have p0015 :=
    @g_rneqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))) p0014
  have p0016 :=
    @g_unieqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))) p0015
  have p0017 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach F C)))
  have p0018 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))
  have p0019 :=
    @g_n_3eqtr4g (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))))) (syn_cwppreach F C) (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) p0016 p0017 p0018
  have p0020 :=
    @g_ineq12d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))) (syn_cwppreach F C) (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) p0007 p0019
  have p0021 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand F C)))
  have p0022 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))
  have p0023 :=
    @g_n_3eqtr4g (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C)) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))) (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))) (syn_cwppcand F C) (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) p0020 p0021 p0022
  have p0024 :=
    @g_id (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))
  have p0025 :=
    @g_sneqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) p0024
  have p0026 :=
    @g_imaeq2d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_csn C) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_ccnv (syn_clec)) p0025
  have p0027 :=
    @g_ineq2d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))) (syn_chwcards (syn_cvv)) p0026
  have p0028 :=
    @g_eqidd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cimage (syn_ccnv F))
  have p0029 :=
    @g_id (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))
  have p0030 :=
    @g_sneqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) p0029
  have p0031 :=
    @g_imaeq2d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_csn C) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_clec) p0030
  have p0032 :=
    @g_jca (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F))) (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))) p0028 p0031
  have p0033 :=
    @g_freceq12 (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))
  have p0034 :=
    @g_syl (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wa (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F))) (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))) (.classEq (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))) p0032 p0033
  have p0035 :=
    @g_rneqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))) p0034
  have p0036 :=
    @g_unieqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))) p0035
  have p0037 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach F C)))
  have p0038 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))
  have p0039 :=
    @g_n_3eqtr4g (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))))) (syn_cwppreach F C) (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) p0036 p0037 p0038
  have p0040 :=
    @g_ineq12d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))) (syn_cwppreach F C) (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) p0027 p0039
  have p0041 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand F C)))
  have p0042 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))))
  have p0043 :=
    @g_n_3eqtr4g (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C)) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))))) (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))) (syn_cwppcand F C) (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) p0040 p0041 p0042
  have p0044 :=
    @g_raleqdv (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wbr (.cv n) (syn_clec) (.cv z)) z (syn_cwppcand F C) (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) dv_cache_0001 dv_cache_0002 p0043
  have p0045 :=
    @g_rexeqbidv (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))) (syn_wral z (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wbr (.cv n) (syn_clec) (.cv z))) n (syn_cwppcand F C) (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0023 p0044
  have p0046 :=
    @g_id (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0047 :=
    @g_eqidd (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) D
  have p0048 :=
    @g_breq12d (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) D D (syn_cwe) p0046 p0047
  have p0049 :=
    @g_eqidd (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) C
  have p0050 :=
    @g_eqidd (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) D
  have p0051 :=
    @g_nceqd (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) D D p0050
  have p0052 :=
    @g_eqeq12d (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) C C (syn_cnc D) (syn_cnc D) p0049 p0051
  have p0053 :=
    @g_anbi12d (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_wbr R (syn_cwe) D) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) D) (.classEq C (syn_cnc D)) (.classEq C (syn_cnc D)) p0048 p0052
  have p0054 :=
    @g_eqidd (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0055 :=
    @g_id (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0056 :=
    @g_breq12d (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cwe) p0054 p0055
  have p0057 :=
    @g_eqidd (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) C
  have p0058 :=
    @g_id (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0059 :=
    @g_nceqd (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0058
  have p0060 :=
    @g_eqeq12d (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) C C (syn_cnc D) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) p0057 p0059
  have p0061 :=
    @g_anbi12d (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) D) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq C (syn_cnc D)) (.classEq C (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) p0056 p0060
  have p0062 :=
    @g_eqidd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0063 :=
    @g_eqidd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0064 :=
    @g_breq12d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cwe) p0062 p0063
  have p0065 :=
    @g_id (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))
  have p0066 :=
    @g_eqidd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0067 :=
    @g_nceqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0066
  have p0068 :=
    @g_eqeq12d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) p0065 p0067
  have p0069 :=
    @g_anbi12d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq C (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) p0064 p0068
  have p0070 :=
    @g_id (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0071 :=
    @g_eqidd (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_c0)
  have p0072 :=
    @g_breq12d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_c0) (syn_c0) (syn_cwe) p0070 p0071
  have p0073 :=
    @g_eqidd (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_cnc (syn_c0))
  have p0074 :=
    @g_eqidd (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_c0)
  have p0075 :=
    @g_nceqd (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_c0) (syn_c0) p0074
  have p0076 :=
    @g_eqeq12d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) p0073 p0075
  have p0077 :=
    @g_anbi12d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) p0072 p0076
  have p0078 :=
    @g_eqidd (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0079 :=
    @g_id (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0080 :=
    @g_breq12d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cwe) p0078 p0079
  have p0081 :=
    @g_eqidd (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cnc (syn_c0))
  have p0082 :=
    @g_id (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0083 :=
    @g_nceqd (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0082
  have p0084 :=
    @g_eqeq12d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) p0081 p0083
  have p0085 :=
    @g_anbi12d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) p0080 p0084
  have p0086 :=
    @g_eqidd (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0087 :=
    @g_eqidd (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0088 :=
    @g_breq12d (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cwe) p0086 p0087
  have p0089 :=
    @g_id (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))
  have p0090 :=
    @g_eqidd (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0091 :=
    @g_nceqd (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0090
  have p0092 :=
    @g_eqeq12d (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) p0089 p0091
  have p0093 :=
    @g_anbi12d (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) p0088 p0092
  have p0094 :=
    @g_wecomparisondefaultemptywe
  have p0095 :=
    @g_eqid (syn_cnc (syn_c0))
  have p0096 :=
    @g_pm3_2i (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) p0094 p0095
  have p0097 :=
    @g_elimhyp3v (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq C (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0)))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0)))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))) R D C (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cnc (syn_c0)) p0053 p0061 p0069 p0077 p0085 p0093 p0096
  have p0098 :=
    @g_simpl (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
  have p0099 :=
    Nominal.mp p0097 p0098
  have p0100 :=
    @g_id (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0101 :=
    @g_eqidd (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) D
  have p0102 :=
    @g_breq12d (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) D D (syn_cwe) p0100 p0101
  have p0103 :=
    @g_eqidd (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) C
  have p0104 :=
    @g_eqidd (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) D
  have p0105 :=
    @g_nceqd (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) D D p0104
  have p0106 :=
    @g_eqeq12d (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) C C (syn_cnc D) (syn_cnc D) p0103 p0105
  have p0107 :=
    @g_anbi12d (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_wbr R (syn_cwe) D) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) D) (.classEq C (syn_cnc D)) (.classEq C (syn_cnc D)) p0102 p0106
  have p0108 :=
    @g_eqidd (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0109 :=
    @g_id (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0110 :=
    @g_breq12d (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cwe) p0108 p0109
  have p0111 :=
    @g_eqidd (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) C
  have p0112 :=
    @g_id (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0113 :=
    @g_nceqd (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0112
  have p0114 :=
    @g_eqeq12d (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) C C (syn_cnc D) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) p0111 p0113
  have p0115 :=
    @g_anbi12d (.classEq D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) D) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq C (syn_cnc D)) (.classEq C (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) p0110 p0114
  have p0116 :=
    @g_eqidd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0117 :=
    @g_eqidd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0118 :=
    @g_breq12d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cwe) p0116 p0117
  have p0119 :=
    @g_id (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))
  have p0120 :=
    @g_eqidd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0121 :=
    @g_nceqd (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0120
  have p0122 :=
    @g_eqeq12d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) p0119 p0121
  have p0123 :=
    @g_anbi12d (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq C (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) p0118 p0122
  have p0124 :=
    @g_id (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0125 :=
    @g_eqidd (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_c0)
  have p0126 :=
    @g_breq12d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_c0) (syn_c0) (syn_cwe) p0124 p0125
  have p0127 :=
    @g_eqidd (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_cnc (syn_c0))
  have p0128 :=
    @g_eqidd (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_c0)
  have p0129 :=
    @g_nceqd (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_c0) (syn_c0) p0128
  have p0130 :=
    @g_eqeq12d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) p0127 p0129
  have p0131 :=
    @g_anbi12d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) p0126 p0130
  have p0132 :=
    @g_eqidd (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0133 :=
    @g_id (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0134 :=
    @g_breq12d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cwe) p0132 p0133
  have p0135 :=
    @g_eqidd (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cnc (syn_c0))
  have p0136 :=
    @g_id (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0137 :=
    @g_nceqd (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0136
  have p0138 :=
    @g_eqeq12d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) p0135 p0137
  have p0139 :=
    @g_anbi12d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) p0134 p0138
  have p0140 :=
    @g_eqidd (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0141 :=
    @g_eqidd (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0142 :=
    @g_breq12d (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cwe) p0140 p0141
  have p0143 :=
    @g_id (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))))
  have p0144 :=
    @g_eqidd (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0145 :=
    @g_nceqd (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0144
  have p0146 :=
    @g_eqeq12d (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) p0143 p0145
  have p0147 :=
    @g_anbi12d (.classEq (syn_cnc (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))) p0142 p0146
  have p0148 :=
    @g_wecomparisondefaultemptywe
  have p0149 :=
    @g_eqid (syn_cnc (syn_c0))
  have p0150 :=
    @g_pm3_2i (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) p0148 p0149
  have p0151 :=
    @g_elimhyp3v (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq C (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0)))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0)))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))) R D C (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cnc (syn_c0)) p0107 p0115 p0123 p0131 p0139 p0147 p0150
  have p0152 :=
    @g_simpr (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))) (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
  have p0153 :=
    Nominal.mp p0151 p0152
  have p0154 :=
    @g_wppcandminfixedpivotdrfdv z (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0))) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) n F dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0099 p0153 hyp_wppcandminfixedpivotpairdrfdv_1
  have p0155 :=
    @g_dedth3v (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) (syn_wrex n (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wral z (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))) (syn_wbr (.cv n) (syn_clec) (.cv z)))) R D C (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cnc (syn_c0)) p0001 p0003 p0045 p0154
  exact p0155

#print axioms g_wppcandminfixedpivotpairdrfdv

end NFChoice.DirectNominalPrf.WPPReplay
