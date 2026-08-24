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
import NominalWPPReplayChunk017Compact001Part036

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

noncomputable def g_hnwcutcodeselfnoisondv
    (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.neg (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_x : h ≠ x := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_h : x ≠ h :=
    Ne.symm fresh_h_ne_x
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_h : u ≠ h :=
    Ne.symm fresh_h_ne_u
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : h ∉ ((syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_u, fresh_h_not_A, fresh_h_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : h ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : h ∉ ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_x, fresh_h_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0001 :=
    @g_hwcnweclndv A (.cv u)
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0004 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0002 p0003
  have p0005 :=
    @g_vex h
  have p0006 :=
    @g_a1i (.classMem (.cv h) (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0005
  have p0007 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv h) (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_strictsegnoiso x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (.cv h)
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv h) (syn_cvv))) (.neg (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0007 p0008
  have p0010 :=
    @g_nexdv (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) h dv_cache_0001 p0009
  have p0011 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0012 :=
    @g_hnwcutcodeambientndv x u A dv_cache_0002
  have p0013 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0011 p0012
  have p0014 :=
    @g_hwnisodirectisobclndv A (.cv u) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) h dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0015 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))))) p0013 p0014
  have p0016 :=
    @g_hnwcutcodepartsndv x u A dv_cache_0002
  have p0017 :=
    @g_simpld (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) p0016
  have p0018 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (.cv h)
  have p0019 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))) p0017 p0018
  have p0020 :=
    @g_hnwcutcodepartsndv x u A dv_cache_0002
  have p0021 :=
    @g_simprd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) p0020
  have p0022 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (.cv h)
  have p0023 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0021 p0022
  have p0024 :=
    @g_bitrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) p0019 p0023
  have p0025 :=
    @g_exbidv (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) h dv_cache_0001 p0024
  have p0026 :=
    @g_bitrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0015 p0025
  have p0027 :=
    @g_biimpd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0026
  have p0028 :=
    @g_mtod (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0010 p0027
  exact p0028

#print axioms g_hnwcutcodeselfnoisondv

end NFChoice.DirectNominalPrf.WPPReplay
