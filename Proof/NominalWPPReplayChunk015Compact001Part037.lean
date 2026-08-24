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
import NominalWPPReplayChunk015Compact001Part036

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

noncomputable def g_wppreachincballfin
    (C : Class) (F : Class) (N : Class) (dv_C_F : Disjoint C.fv F.fv) (hyp_wppreachincballfin_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachincballfin_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem N (syn_cwppreachincb F C))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  let d : Var := freshVar proofSupport 2
  let e : Var := freshVar proofSupport 3
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_N : d ∉ N.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_e_not_F : e ∉ F.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e_not_N : e ∉ N.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_ne_d : n ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_d_ne_n : d ≠ n :=
    Ne.symm fresh_n_ne_d
  have fresh_n_ne_e : n ≠ e := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_e_ne_n : e ≠ n :=
    Ne.symm fresh_n_ne_e
  have fresh_m_ne_d : m ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_d_ne_m : d ≠ m :=
    Ne.symm fresh_m_ne_d
  have fresh_m_ne_e : m ≠ e := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_e_ne_m : e ≠ m :=
    Ne.symm fresh_m_ne_e
  have fresh_d_ne_e : d ≠ e := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_e_ne_d : e ≠ d :=
    Ne.symm fresh_d_ne_e
  have dv_cache_0001 : n ∉ ((syn_cwppreachincb F C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint (C).fv (F).fv := by
    clear dv_cache_0001
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0003 : d ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : Disjoint (C).fv ((syn_ctc (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (C).fv ((syn_ctc (.cv m))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc]; exact (show Disjoint ((C).fv) (((Class.cv m)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((C).fv) (({m} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show m ∉ (C).fv from (by exact fresh_m_not_C))))))))
  have dv_cache_0007 : Disjoint (F).fv ((syn_ctc (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (F).fv ((syn_ctc (.cv m))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc]; exact (show Disjoint ((F).fv) (((Class.cv m)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((F).fv) (({m} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show m ∉ (F).fv from (by exact fresh_m_not_F))))))))
  have dv_cache_0008 : e ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : e ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : e ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : e ∉ ((syn_cfv F (.cv d))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_d, fresh_e_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : e ∉ ((syn_cdm F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : e ∉ ((syn_wb (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_d, fresh_e_not_F, fresh_e_ne_m, fresh_e_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : d ∉ ((syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_m, fresh_d_not_C, fresh_d_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : d ∉ ((syn_cplc (.cv m) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : n ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : n ∉ ((Wff.classMem (.cv m) (syn_cwppreachincb F C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : m ∉ ((Wff.classMem (.cv n) (syn_cwppreachincb F C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, fresh_m_not_C, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : n ∉ ((Wff.classMem (syn_c0c) (syn_cwppreachincb F C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : n ∉ ((Wff.classMem N (syn_cwppreachincb F C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : n ∉ ((Wff.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : n ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have p0000 :=
    @g_elex F (syn_cfuns)
  have p0001 :=
    Nominal.mp hyp_wppreachincballfin_1 p0000
  have p0002 :=
    @g_wppreachincbex C F p0001
  have p0003 :=
    @g_abid2 n (syn_cwppreachincb F C) dv_cache_0001
  have p0004 :=
    @g_eleq1i (.cab n (.classMem (.cv n) (syn_cwppreachincb F C))) (syn_cwppreachincb F C) (syn_cvv) p0003
  have p0005 :=
    @g_mpbir (.classMem (.cab n (.classMem (.cv n) (syn_cwppreachincb F C))) (syn_cvv)) (.classMem (syn_cwppreachincb F C) (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_id (.classEq (.cv n) (syn_c0c))
  have p0007 :=
    @g_eleq1d (.classEq (.cv n) (syn_c0c)) (.cv n) (syn_c0c) (syn_cwppreachincb F C) p0006
  have p0008 :=
    @g_id (.classEq (.cv n) (.cv m))
  have p0009 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (syn_cwppreachincb F C) p0008
  have p0010 :=
    @g_id (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
  have p0011 :=
    @g_eleq1d (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C) p0010
  have p0012 :=
    @g_id (.classEq (.cv n) N)
  have p0013 :=
    @g_eleq1d (.classEq (.cv n) N) (.cv n) N (syn_cwppreachincb F C) p0012
  have p0014 :=
    @g_tc0c
  have p0015 :=
    @g_fveq2i (syn_ctc (syn_c0c)) (syn_c0c) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0014
  have p0016 :=
    @g_elex F (syn_cfuns)
  have p0017 :=
    Nominal.mp hyp_wppreachincballfin_1 p0016
  have p0018 :=
    @g_wppreach0 C F dv_cache_0002 p0017
  have p0019 :=
    @g_eqtri (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_c0c))) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_c0c)) (syn_cima (syn_clec) (syn_csn C)) p0015 p0018
  have p0020 :=
    @g_peano1
  have p0021 :=
    @g_elex F (syn_cfuns)
  have p0022 :=
    Nominal.mp hyp_wppreachincballfin_1 p0021
  have p0023 :=
    @g_wpppowlayerseqfvcl (syn_c0c) C F dv_cache_0002 p0022
  have p0024 :=
    Nominal.mp p0020 p0023
  have p0025 :=
    @g_tc0c
  have p0026 :=
    @g_fveq2i (syn_ctc (syn_c0c)) (syn_c0c) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0025
  have p0027 :=
    @g_elex F (syn_cfuns)
  have p0028 :=
    Nominal.mp hyp_wppreachincballfin_1 p0027
  have p0029 :=
    @g_wpppowcore0 F p0028
  have p0030 :=
    @g_eqtri (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid) p0026 p0029
  have p0031 :=
    @g_cnveqi (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))) (syn_cid) p0030
  have p0032 :=
    @g_cnvi
  have p0033 :=
    @g_eqtri (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))) (syn_ccnv (syn_cid)) (syn_cid) p0031 p0032
  have p0034 :=
    @g_imaeq1i (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))) (syn_cid) (syn_cima (syn_clec) (syn_csn C)) p0033
  have p0035 :=
    @g_imai (syn_cima (syn_clec) (syn_csn C))
  have p0036 :=
    @g_eqtri (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_cid) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_clec) (syn_csn C)) p0034 p0035
  have p0037 :=
    @g_eqtri (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_clec) (syn_csn C)) p0024 p0036
  have p0038 :=
    @g_eqcomi (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c))) (syn_cima (syn_clec) (syn_csn C)) p0037
  have p0039 :=
    @g_eqtri (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_c0c))) (syn_cima (syn_clec) (syn_csn C)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c))) p0019 p0038
  have p0040 :=
    @g_eleq2i (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_c0c))) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c))) (.cv d) p0039
  have p0041 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_c0c)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c))))) (.classMem (.cv d) (syn_cdm F)) p0040
  have p0042 :=
    @g_rgen (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_c0c)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c))))) d (syn_cdm F) p0041
  have p0043 :=
    @g_peano1
  have p0044 :=
    @g_elex F (syn_cfuns)
  have p0045 :=
    Nominal.mp hyp_wppreachincballfin_1 p0044
  have p0046 :=
    @g_wppreachincblayerscl (syn_c0c) C F d dv_cache_0003 dv_cache_0002 dv_cache_0004 dv_cache_0005 p0045
  have p0047 :=
    Nominal.mp p0043 p0046
  have p0048 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_c0c)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_c0c)))))) p0042 p0047
  have p0049 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))
  have p0050 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))
  have p0051 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv m) (syn_cnnc)) p0049 p0050
  have p0052 :=
    @g_nntcsuc (.cv m)
  have p0053 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) p0051 p0052
  have p0054 :=
    @g_fveq2d (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0053
  have p0055 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))
  have p0056 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))
  have p0057 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv m) (syn_cnnc)) p0055 p0056
  have p0058 :=
    @g_nntccl (.cv m)
  have p0059 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0057 p0058
  have p0060 :=
    @g_elex F (syn_cfuns)
  have p0061 :=
    Nominal.mp hyp_wppreachincballfin_1 p0060
  have p0062 :=
    @g_wppreachsucndv C F (syn_ctc (.cv m)) dv_cache_0002 dv_cache_0006 dv_cache_0007 p0061
  have p0063 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (syn_cima (syn_ccnv F) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m))))) p0059 p0062
  have p0064 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (syn_cima (syn_ccnv F) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) p0054 p0063
  have p0065 :=
    @g_eleq2d (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_cima (syn_ccnv F) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.cv d) p0064
  have p0066 :=
    @g_elfunsi F
  have p0067 :=
    Nominal.mp hyp_wppreachincballfin_1 p0066
  have p0068 :=
    @g_funfn F
  have p0069 :=
    @g_biimpi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0068
  have p0070 :=
    Nominal.mp p0067 p0069
  have p0071 :=
    @g_elpreima (syn_cdm F) (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m))) F
  have p0072 :=
    Nominal.mp p0070 p0071
  have p0073 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m))))) (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) p0072
  have p0074 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))
  have p0075 :=
    @g_biantrurd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) p0074
  have p0076 :=
    @g_bicomd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m))))) p0075
  have p0077 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m))))) (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m))))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) p0073 p0076
  have p0078 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m))))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) p0065 p0077
  have p0079 :=
    @g_elfunsi F
  have p0080 :=
    Nominal.mp hyp_wppreachincballfin_1 p0079
  have p0081 :=
    @g_a1i (syn_wfun F) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) p0080
  have p0082 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))
  have p0083 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_wfun F) (.classMem (.cv d) (syn_cdm F)) p0081 p0082
  have p0084 :=
    @g_fvelrn (.cv d) F
  have p0085 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_wa (syn_wfun F) (.classMem (.cv d) (syn_cdm F))) (.classMem (syn_cfv F (.cv d)) (syn_crn F)) p0083 p0084
  have p0086 :=
    @g_sseli (syn_crn F) (syn_cdm F) (syn_cfv F (.cv d)) hyp_wppreachincballfin_2
  have p0087 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (syn_cfv F (.cv d)) (syn_crn F)) (.classMem (syn_cfv F (.cv d)) (syn_cdm F)) p0085 p0086
  have p0088 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))
  have p0089 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))
  have p0090 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))
  have p0091 :=
    @g_elex F (syn_cfuns)
  have p0092 :=
    Nominal.mp hyp_wppreachincballfin_1 p0091
  have p0093 :=
    @g_wppreachincblayerscl (.cv m) C F e dv_cache_0008 dv_cache_0002 dv_cache_0009 dv_cache_0010 p0092
  have p0094 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv m) (syn_cnnc)) (syn_wb (.classMem (.cv m) (syn_cwppreachincb F C)) (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))))) p0090 p0093
  have p0095 :=
    @g_biimpd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv m) (syn_cwppreachincb F C)) (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))) p0094
  have p0096 :=
    @g_mpd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv m) (syn_cwppreachincb F C)) (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))) p0089 p0095
  have p0097 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))) p0088 p0096
  have p0098 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (syn_cfv F (.cv d)) (syn_cdm F)) (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))) p0087 p0097
  have p0099 :=
    @g_id (.classEq (.cv e) (syn_cfv F (.cv d)))
  have p0100 :=
    @g_eleq1d (.classEq (.cv e) (syn_cfv F (.cv d))) (.cv e) (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m))) p0099
  have p0101 :=
    @g_id (.classEq (.cv e) (syn_cfv F (.cv d)))
  have p0102 :=
    @g_eleq1d (.classEq (.cv e) (syn_cfv F (.cv d))) (.cv e) (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))) p0101
  have p0103 :=
    @g_bibi12d (.classEq (.cv e) (syn_cfv F (.cv d))) (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))) p0100 p0102
  have p0104 :=
    @g_rspcva (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) (syn_wb (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) e (syn_cfv F (.cv d)) (syn_cdm F) dv_cache_0011 dv_cache_0012 dv_cache_0013 p0103
  have p0105 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_wa (.classMem (syn_cfv F (.cv d)) (syn_cdm F)) (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))))) (syn_wb (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) p0098 p0104
  have p0106 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv m)))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))) p0078 p0105
  have p0107 :=
    @g_elfunsi F
  have p0108 :=
    Nominal.mp hyp_wppreachincballfin_1 p0107
  have p0109 :=
    @g_funfn F
  have p0110 :=
    @g_biimpi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0109
  have p0111 :=
    Nominal.mp p0108 p0110
  have p0112 :=
    @g_elpreima (syn_cdm F) (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))) F
  have p0113 :=
    Nominal.mp p0111 p0112
  have p0114 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) p0113
  have p0115 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))
  have p0116 :=
    @g_biantrurd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))) p0115
  have p0117 :=
    @g_bicomd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))) (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) p0116
  have p0118 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) (syn_wa (.classMem (.cv d) (syn_cdm F)) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))) p0114 p0117
  have p0119 :=
    @g_bicomd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))) p0118
  have p0120 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (syn_cfv F (.cv d)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))) (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) p0106 p0119
  have p0121 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))
  have p0122 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))
  have p0123 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv m) (syn_cnnc)) p0121 p0122
  have p0124 :=
    @g_elex F (syn_cfuns)
  have p0125 :=
    Nominal.mp hyp_wppreachincballfin_1 p0124
  have p0126 :=
    @g_wpppowlayerseqsuc C m F dv_cache_0002 p0125
  have p0127 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c)))) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) p0123 p0126
  have p0128 :=
    @g_eleq2d (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c)))) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m)))) (.cv d) p0127
  have p0129 :=
    @g_bicomd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) p0128
  have p0130 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv d) (syn_cdm F))) (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv d) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv m))))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c))))) p0120 p0129
  have p0131 :=
    @g_ralrimiva (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c)))))) d (syn_cdm F) dv_cache_0014 p0130
  have p0132 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))
  have p0133 :=
    @g_peano2 (.cv m)
  have p0134 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) p0132 p0133
  have p0135 :=
    @g_elex F (syn_cfuns)
  have p0136 :=
    Nominal.mp hyp_wppreachincballfin_1 p0135
  have p0137 :=
    @g_wppreachincblayerscl (syn_cplc (.cv m) (syn_c1c)) C F d dv_cache_0015 dv_cache_0002 dv_cache_0004 dv_cache_0005 p0136
  have p0138 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (syn_wb (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c)))))))) p0134 p0137
  have p0139 :=
    @g_mpbird (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C))) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv m) (syn_c1c))))))) p0131 p0138
  have p0140 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwppreachincb F C)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C)) p0139
  have p0141_e02_recanon : Nominal.NPrf (.imp (.objEq n m) (syn_wb (.classMem (.cv n) (syn_cwppreachincb F C)) (.classMem (.cv m) (syn_cwppreachincb F C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwppreachincb syn_cuni1 syn_cuni syn_wex syn_wa syn_cin syn_ccompl syn_cnin syn_wnan syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0141 :=
    @g_finds (.classMem (.cv n) (syn_cwppreachincb F C)) (.classMem (syn_c0c) (syn_cwppreachincb F C)) (.classMem (.cv m) (syn_cwppreachincb F C)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwppreachincb F C)) (.classMem N (syn_cwppreachincb F C)) n m N dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 p0005 p0007 p0141_e02_recanon p0011 p0013 p0048 p0140
  exact p0141

noncomputable def g_wppreachpowlayers
    (C : Class) (F : Class) (N : Class) (d : Var) (dv_C_F : Disjoint C.fv F.fv) (dv_C_d : d ∉ C.fv) (dv_F_d : d ∉ F.fv) (dv_N_d : d ∉ N.fv) (hyp_wppreachpowlayers_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachpowlayers_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ N.fv ∪ ({d} : Finset Var)
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : d ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : d ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppreachincballfin C F N dv_cache_0001 hyp_wppreachpowlayers_1 hyp_wppreachpowlayers_2
  have p0001 :=
    @g_elex F (syn_cfuns)
  have p0002 :=
    Nominal.mp hyp_wppreachpowlayers_1 p0001
  have p0003 :=
    @g_wppreachincblayerscl N C F d dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004 p0002
  have p0004 :=
    @g_mpbid (.classMem N (syn_cnnc)) (.classMem N (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))))) p0000 p0003
  exact p0004

noncomputable def g_wpppowlayerorbcl
    (B : Class) (C : Class) (D : Class) (F : Class) (dv_C_F : Disjoint C.fv F.fv) (hyp_wpppowlayerorbcl_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wpppowlayerorbcl_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wpppowlayerorbcl_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B)))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : n ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, fresh_n_not_D, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem B (syn_cnnc))
  have p0001 :=
    @g_id (.classEq (.cv n) B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0003 :=
    @g_id (.classEq (.cv n) B)
  have p0004 :=
    @g_sneqd (.classEq (.cv n) B) (.cv n) B p0003
  have p0005 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_csn (.cv n)) (syn_csn B) (syn_cwpppowlayerseq F C) p0004
  have p0006 :=
    @g_eleq2d (.classEq (.cv n) B) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) D p0005
  have p0007 :=
    @g_id (.classEq (.cv n) B)
  have p0008 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec F D) p0007
  have p0009 :=
    @g_breq2d (.classEq (.cv n) B) (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cfv (syn_cfrec F D) B) C (syn_clec) p0008
  have p0010 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B)) p0006 p0009
  have p0011 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B))) p0002 p0010
  have p0012 :=
    @g_wpppowlayerorb C D n F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wpppowlayerorbcl_1 hyp_wpppowlayerorbcl_2 hyp_wpppowlayerorbcl_3
  have p0013 :=
    @g_vtoclg (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))) (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B)))) n B (syn_cnnc) dv_cache_0004 dv_cache_0005 p0011 p0012
  have p0014 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) B))) p0000 p0013
  exact p0014

#print axioms g_wpppowlayerorbcl

end NFChoice.DirectNominalPrf.WPPReplay
