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
import NominalWPPReplayChunk016Compact001Part036

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

noncomputable def g_wecomparisonterminalfdv
    (x : Var) (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_h : h ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_h_x : h ≠ x) (hyp_wecomparisonterminalfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecomparisonterminalfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({h} : Finset Var) ∪ E.fv
  have dv_cache_0001 : h ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : h ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : h ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : h ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ x from (by exact dv_h_x))
  have p0000 :=
    @g_wecutisouniex D R S E hyp_wecomparisonterminalfdv_1 hyp_wecomparisonterminalfdv_2
  have p0001 :=
    @g_wecomparisonterminalsetfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_wecomparisonterminalfdv_1 hyp_wecomparisonterminalfdv_2 p0000
  exact p0001

noncomputable def g_weisoexnceqclfdv
    (A : Class) (B : Class) (T : Class) (U : Class) (h : Var) (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) :
    Nominal.NPrf (.imp (syn_wex h (syn_wiso (.cv h) T U A B)) (.classEq (syn_cnc A) (syn_cnc B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ T.fv ∪ U.fv ∪ ({h} : Finset Var)
  have dv_cache_0001 : h ∉ ((Wff.classEq (syn_cnc A) (syn_cnc B))).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, dv_B_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_isof1o A B T U (.cv h)
  have p0001 :=
    @g_vex h
  have p0002 :=
    @g_f1oen A B (.cv h) p0001
  have p0003 :=
    @g_syl (syn_wiso (.cv h) T U A B) (syn_wf1o (.cv h) A B) (syn_wbr A (syn_cen) B) p0000 p0002
  have p0004 :=
    @g_isof1o A B T U (.cv h)
  have p0005 :=
    @g_vex h
  have p0006 :=
    @g_f1oen A B (.cv h) p0005
  have p0007 :=
    @g_syl (syn_wiso (.cv h) T U A B) (syn_wf1o (.cv h) A B) (syn_wbr A (syn_cen) B) p0004 p0006
  have p0008 :=
    @g_breldm A B (syn_cen)
  have p0009 :=
    @g_syl (syn_wiso (.cv h) T U A B) (syn_wbr A (syn_cen) B) (.classMem A (syn_cdm (syn_cen))) p0007 p0008
  have p0010 :=
    @g_dmen
  have p0011 :=
    @g_eleq2i (syn_cdm (syn_cen)) (syn_cvv) A p0010
  have p0012 :=
    @g_biimpi (.classMem A (syn_cdm (syn_cen))) (.classMem A (syn_cvv)) p0011
  have p0013 :=
    @g_syl (syn_wiso (.cv h) T U A B) (.classMem A (syn_cdm (syn_cen))) (.classMem A (syn_cvv)) p0009 p0012
  have p0014 :=
    @g_eqncg A B (syn_cvv)
  have p0015 :=
    @g_syl (syn_wiso (.cv h) T U A B) (.classMem A (syn_cvv)) (syn_wb (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B)) p0013 p0014
  have p0016 :=
    @g_mpbird (syn_wiso (.cv h) T U A B) (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B) p0003 p0015
  have p0017 :=
    @g_exlimiv (syn_wiso (.cv h) T U A B) (.classEq (syn_cnc A) (syn_cnc B)) h dv_cache_0001 p0016
  exact p0017

noncomputable def g_wecomparisonforwardnclecclfdv
    (x : Var) (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_h : h ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_h_x : h ≠ x) (hyp_wecomparisonforwardnclecclfdv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.imp (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({h} : Finset Var) ∪ E.fv
  have dv_cache_0001 : h ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ (E).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_h, dv_S_h, dv_h_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex S E (syn_cwe)
  have p0001 :=
    Nominal.mp hyp_wecomparisonforwardnclecclfdv_1 p0000
  have p0002 :=
    @g_simpri (.classMem S (syn_cvv)) (.classMem E (syn_cvv)) p0001
  have p0003 :=
    @g_ncelncsi E p0002
  have p0004 :=
    @g_nclecid (syn_cnc E)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_weisoexnceqclfdv D E R S h dv_cache_0001 dv_cache_0002
  have p0007 :=
    @g_breq1d (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_cnc D) (syn_cnc E) (syn_cnc E) (syn_clec) p0006
  have p0008 :=
    @g_mpbiri (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc E)) p0005 p0007
  have p0009 :=
    @g_inss1 E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))
  have p0010 :=
    @g_brex S E (syn_cwe)
  have p0011 :=
    Nominal.mp hyp_wecomparisonforwardnclecclfdv_1 p0010
  have p0012 :=
    @g_simpri (.classMem S (syn_cvv)) (.classMem E (syn_cvv)) p0011
  have p0013 :=
    @g_brex S E (syn_cwe)
  have p0014 :=
    Nominal.mp hyp_wecomparisonforwardnclecclfdv_1 p0013
  have p0015 :=
    @g_simpli (.classMem S (syn_cvv)) (.classMem E (syn_cvv)) p0014
  have p0016 :=
    @g_idex
  have p0017 :=
    @g_difex S (syn_cid) p0015 p0016
  have p0018 :=
    @g_cnvex (syn_cdif S (syn_cid)) p0017
  have p0019 :=
    @g_snex (.cv x)
  have p0020 :=
    @g_imaex (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)) p0018 p0019
  have p0021 :=
    @g_inex E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) p0012 p0020
  have p0022 :=
    @g_brex S E (syn_cwe)
  have p0023 :=
    Nominal.mp hyp_wecomparisonforwardnclecclfdv_1 p0022
  have p0024 :=
    @g_simpri (.classMem S (syn_cvv)) (.classMem E (syn_cvv)) p0023
  have p0025 :=
    @g_nclec (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) E p0021 p0024
  have p0026 :=
    Nominal.mp p0009 p0025
  have p0027 :=
    @g_weisoexnceqclfdv D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) h dv_cache_0001 dv_cache_0003
  have p0028 :=
    @g_breq1d (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_cnc D) (syn_cnc (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) (syn_cnc E) (syn_clec) p0027
  have p0029 :=
    @g_mpbiri (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wbr (syn_cnc (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) (syn_clec) (syn_cnc E)) p0026 p0028
  have p0030 :=
    @g_rexlimivw (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) x E dv_cache_0004 p0029
  have p0031 :=
    @g_jaoi (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) p0008 p0030
  exact p0031

noncomputable def g_wecomparisonreversecutrepfdv
    (x : Var) (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_h_x : h ≠ x) :
    Nominal.NPrf (.imp (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({h} : Finset Var) ∪ E.fv
  have dv_cache_0001 : h ∉ (E).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, dv_R_h, dv_h_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_weisoexnceqclfdv E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) h dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_reximi (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) x D p0000
  exact p0001

noncomputable def g_wecomparisoncutrepltfdv
    (x : Var) (D : Class) (R : Class) (S : Class) (E : Class) (dv_D_x : x ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_R_x : x ∉ R.fv) (dv_S_x : x ∉ S.fv) (hyp_wecomparisoncutrepltfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecomparisoncutrepltfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) (hyp_wecomparisoncutrepltfdv_3 : Nominal.NPrf (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) :
    Nominal.NPrf (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_x : h ≠ x := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_h : x ≠ h :=
    Ne.symm fresh_h_ne_x
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_h_not_R : h ∉ R.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_S : h ∉ S.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_E : h ∉ E.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : h ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : h ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : h ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : h ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have p0000 :=
    @g_wecomparisonterminalfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_wecomparisoncutrepltfdv_1 hyp_wecomparisoncutrepltfdv_2
  have p0001 :=
    @g_orc (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
  have p0002 :=
    @g_wecomparisonforwardnclecclfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_wecomparisoncutrepltfdv_2
  have p0003 :=
    @g_brex S E (syn_cwe)
  have p0004 :=
    Nominal.mp hyp_wecomparisoncutrepltfdv_2 p0003
  have p0005 :=
    @g_simpri (.classMem S (syn_cvv)) (.classMem E (syn_cvv)) p0004
  have p0006 :=
    @g_ncelncsi E p0005
  have p0007 :=
    @g_brex R D (syn_cwe)
  have p0008 :=
    Nominal.mp hyp_wecomparisoncutrepltfdv_1 p0007
  have p0009 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0008
  have p0010 :=
    @g_ncelncsi D p0009
  have p0011 :=
    @g_pm3_2i (.classMem (syn_cnc E) (syn_cncs)) (.classMem (syn_cnc D) (syn_cncs)) p0006 p0010
  have p0012 :=
    @g_ltlenlec (syn_cnc E) (syn_cnc D)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_biimpi (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) (syn_wa (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D)) (.neg (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)))) p0013
  have p0015 :=
    Nominal.mp hyp_wecomparisoncutrepltfdv_3 p0014
  have p0016 :=
    @g_simpri (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D)) (.neg (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))) p0015
  have p0017 :=
    @g_pm2_21 (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_syl (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0002 p0018
  have p0020 :=
    @g_syl (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0001 p0019
  have p0021 :=
    @g_olc (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wex h (syn_wiso (.cv h) R S D E))
  have p0022 :=
    @g_wecomparisonforwardnclecclfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_wecomparisoncutrepltfdv_2
  have p0023 :=
    @g_brex S E (syn_cwe)
  have p0024 :=
    Nominal.mp hyp_wecomparisoncutrepltfdv_2 p0023
  have p0025 :=
    @g_simpri (.classMem S (syn_cvv)) (.classMem E (syn_cvv)) p0024
  have p0026 :=
    @g_ncelncsi E p0025
  have p0027 :=
    @g_brex R D (syn_cwe)
  have p0028 :=
    Nominal.mp hyp_wecomparisoncutrepltfdv_1 p0027
  have p0029 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0028
  have p0030 :=
    @g_ncelncsi D p0029
  have p0031 :=
    @g_pm3_2i (.classMem (syn_cnc E) (syn_cncs)) (.classMem (syn_cnc D) (syn_cncs)) p0026 p0030
  have p0032 :=
    @g_ltlenlec (syn_cnc E) (syn_cnc D)
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_biimpi (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) (syn_wa (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D)) (.neg (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)))) p0033
  have p0035 :=
    Nominal.mp hyp_wecomparisoncutrepltfdv_3 p0034
  have p0036 :=
    @g_simpri (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D)) (.neg (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))) p0035
  have p0037 :=
    @g_pm2_21 (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_syl (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0022 p0038
  have p0040 :=
    @g_syl (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0021 p0039
  have p0041 :=
    @g_wecomparisonreversecutrepfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0009
  have p0042 :=
    @g_n_3jaoi (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0020 p0040 p0041
  have p0043 :=
    Nominal.mp p0000 p0042
  exact p0043

#print axioms g_wecomparisoncutrepltfdv

end NFChoice.DirectNominalPrf.WPPReplay
