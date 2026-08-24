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
import NominalWPPReplayChunk013Compact001Part060

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

noncomputable def g_csucex
    (x : Var) :
    Nominal.NPrf (.classMem (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_singleton.mpr h)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_singleton.mpr h)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_singleton.mpr h)
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : x ∉ ((Class.cv w)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_cop (.cv y) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((syn_ccnv (syn_c1st))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((syn_cplc (.cv x) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0014 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Wff.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (syn_ccnv (syn_c1st)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (syn_ccnv (syn_c1st)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_brcnv (.cv y) (.cv w) (syn_c1st)
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_br1st x (.cv w) (.cv y) dv_cache_0001 dv_cache_0002 p0001
  have p0003 :=
    @g_bitri (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y)) (syn_wex x (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))) p0000 p0002
  have p0004 :=
    @g_anbi1i (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wex x (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)) p0003
  have p0005 :=
    @g_n_19_41v (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)) x dv_cache_0003
  have p0006 :=
    @g_bitr4i (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))) (syn_wa (syn_wex x (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))) (syn_wex x (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)))) p0004 p0005
  have p0007 :=
    @g_exbii (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))) (syn_wex x (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)))) w p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))) w x
  have p0009 :=
    @g_vex x
  have p0010 :=
    @g_opex (.cv y) (.cv x) p0001 p0009
  have p0011 :=
    @g_breq1 (.cv w) (syn_cop (.cv y) (.cv x)) (.cv z) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
  have p0012 :=
    @g_brres (syn_cop (.cv y) (.cv x)) (.cv z) (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))
  have p0013 :=
    @g_braddcfn (.cv y) (.cv x) (.cv z) p0001 p0009
  have p0014 :=
    @g_opelxp (.cv y) (.cv x) (syn_cvv) (syn_csn (syn_c1c))
  have p0015 :=
    @g_mpbiran (.classMem (syn_cop (.cv y) (.cv x)) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_csn (syn_c1c))) p0001 p0014
  have p0016 :=
    @g_elsn x (syn_c1c) dv_cache_0004
  have p0017 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv x)) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.classMem (.cv x) (syn_csn (syn_c1c))) (.classEq (.cv x) (syn_c1c)) p0015 p0016
  have p0018 :=
    @g_anbi12ci (syn_wbr (syn_cop (.cv y) (.cv x)) (syn_caddcfn) (.cv z)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)) (.classMem (syn_cop (.cv y) (.cv x)) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.classEq (.cv x) (syn_c1c)) p0013 p0017
  have p0019 :=
    @g_bitri (syn_wbr (syn_cop (.cv y) (.cv x)) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)) (syn_wa (syn_wbr (syn_cop (.cv y) (.cv x)) (syn_caddcfn) (.cv z)) (.classMem (syn_cop (.cv y) (.cv x)) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))) (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z))) p0012 p0018
  have p0020 :=
    @g_syl6bb (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)) (syn_wbr (syn_cop (.cv y) (.cv x)) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)) (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z))) p0011 p0019
  have p0021 :=
    @g_ceqsexv (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)) (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z))) w (syn_cop (.cv y) (.cv x)) dv_cache_0005 dv_cache_0006 p0010 p0020
  have p0022 :=
    @g_exbii (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)))) (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z))) x p0021
  have p0023 :=
    @g_bitri (syn_wex w (syn_wex x (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))))) (syn_wex x (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)))) p0008 p0022
  have p0024 :=
    @g_bitri (syn_wex w (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)))) (syn_wex w (syn_wex x (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)))) p0007 p0023
  have p0025 :=
    @g_n_1cex
  have p0026 :=
    @g_addceq2 (.cv x) (syn_c1c) (.cv y)
  have p0027 :=
    @g_eqeq1d (.classEq (.cv x) (syn_c1c)) (syn_cplc (.cv y) (.cv x)) (syn_cplc (.cv y) (syn_c1c)) (.cv z) p0026
  have p0028 :=
    @g_ceqsexv (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)) (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) x (syn_c1c) dv_cache_0004 dv_cache_0007 p0025 p0027
  have p0029 :=
    @g_bitri (syn_wex w (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) p0024 p0028
  have p0030 :=
    @g_opelco w (.cv y) (.cv z) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (syn_ccnv (syn_c1st)) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0031 :=
    @g_mptv x w (syn_cplc (.cv x) (syn_c1c)) dv_cache_0012 dv_cache_0013
  have p0032 :=
    @g_eleq2i (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (syn_copab x w (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))) (syn_cop (.cv y) (.cv z)) p0031
  have p0033 :=
    @g_vex z
  have p0034 :=
    @g_addceq1 (.cv x) (.cv y) (syn_c1c)
  have p0035_e00_recanon : Nominal.NPrf (.imp (.objEq x y) (.classEq (syn_cplc (.cv x) (syn_c1c)) (syn_cplc (.cv y) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0034
  have p0035 :=
    @g_eqeq2d (.objEq x y) (syn_cplc (.cv x) (syn_c1c)) (syn_cplc (.cv y) (syn_c1c)) (.cv w) p0035_e00_recanon
  have p0036 :=
    @g_eqeq1 (.cv w) (.cv z) (syn_cplc (.cv y) (syn_c1c))
  have p0037 :=
    @g_eqcom (.cv z) (syn_cplc (.cv y) (syn_c1c))
  have p0038_e00_recanon : Nominal.NPrf (.imp (.objEq w z) (syn_wb (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c))) (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0036
  have p0038 :=
    @g_syl6bb (.objEq w z) (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c))) (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) p0038_e00_recanon p0037
  have p0039_e02_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0035
  have p0039_e03_recanon : Nominal.NPrf (.imp (.classEq (.cv w) (.cv z)) (syn_wb (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0038
  have p0039 :=
    @g_opelopab (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) x w (.cv y) (.cv z) dv_cache_0002 dv_cache_0008 dv_cache_0014 dv_cache_0009 dv_cache_0007 dv_cache_0015 dv_cache_0013 p0001 p0033 p0039_e02_recanon p0039_e03_recanon
  have p0040 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv z)) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))) (.classMem (syn_cop (.cv y) (.cv z)) (syn_copab x w (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) p0032 p0039
  have p0041 :=
    @g_n_3bitr4ri (syn_wex w (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (syn_ccnv (syn_c1st)))) (.classMem (syn_cop (.cv y) (.cv z)) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))) p0029 p0030 p0040
  have p0042 :=
    @g_eqrelriv y z (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (syn_ccnv (syn_c1st))) dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0041
  have p0043 :=
    @g_addcfnex
  have p0044 :=
    @g_vvex
  have p0045 :=
    @g_snex (syn_c1c)
  have p0046 :=
    @g_xpex (syn_cvv) (syn_csn (syn_c1c)) p0044 p0045
  have p0047 :=
    @g_resex (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))) p0043 p0046
  have p0048 :=
    @g_n_1stex
  have p0049 :=
    @g_cnvex (syn_c1st) p0048
  have p0050 :=
    @g_coex (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (syn_ccnv (syn_c1st)) p0047 p0049
  have p0051 :=
    @g_eqeltri (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (syn_ccnv (syn_c1st))) (syn_cvv) p0042 p0050
  exact p0051

noncomputable def g_brcsuc
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_brcsuc_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_brcsuc_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) B) (.classEq B (syn_cplc A (syn_c1c)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((syn_cplc (.cv x) (syn_c1c))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq B (syn_cplc A (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classEq B (syn_cplc A (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_addceq1 (.cv x) A (syn_c1c)
  have p0001 :=
    @g_eqeq2d (.classEq (.cv x) A) (syn_cplc (.cv x) (syn_c1c)) (syn_cplc A (syn_c1c)) (.cv y) p0000
  have p0002 :=
    @g_eqeq1 (.cv y) B (syn_cplc A (syn_c1c))
  have p0003 :=
    @g_mptv x y (syn_cplc (.cv x) (syn_c1c)) dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_brab (.classEq (.cv y) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv y) (syn_cplc A (syn_c1c))) (.classEq B (syn_cplc A (syn_c1c))) x y A B (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0002 hyp_brcsuc_1 hyp_brcsuc_2 p0001 p0002 p0003
  exact p0004

#print axioms g_brcsuc

end NFChoice.DirectNominalPrf.WPPReplay
