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
import NominalWPPReplayChunk016Compact001Part046

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

noncomputable def g_wppgammaimagetceqndv
    (C : Class) (k : Var) (F : Class) (G : Class) (d : Var) (dv_C_d : d ∉ C.fv) (dv_C_k : k ∉ C.fv) (dv_F_d : d ∉ F.fv) (dv_F_k : k ∉ F.fv) (dv_G_d : d ∉ G.fv) (dv_G_k : k ∉ G.fv) (dv_d_k : d ≠ k) (hyp_wppgammaimagetceqndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wppgammaimagetceqndv_2 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) (hyp_wppgammaimagetceqndv_3 : Nominal.NPrf (.classMem G (syn_cvv))) (hyp_wppgammaimagetceqndv_4 : Nominal.NPrf (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))) (hyp_wppgammaimagetceqndv_5 : Nominal.NPrf (.all k (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d))))))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_cwppgamma G (syn_ctc C))) := by
  let proofSupport : Finset Var := C.fv ∪ ({k} : Finset Var) ∪ F.fv ∪ G.fv ∪ ({d} : Finset Var)
  have dv_cache_0001 : k ∉ ((syn_ctc C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : k ∉ (G).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0005 : d ∉ ((syn_cwppgamma F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : d ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : d ∉ ((Wff.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (syn_cwppgamma F C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : d ∉ ((Wff.classEq (.cv k) (syn_ctc (syn_cwppgamma F C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_k, dv_C_d, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : k ∉ ((syn_ctc (syn_cwppgamma F C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : k ∉ ((syn_wb (.classMem (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C))) (syn_wrex d (syn_cwppcand F C) (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, dv_G_k, (Ne.symm dv_d_k), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, dv_F_d, dv_d_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : k ∉ ((syn_cwppgamma G (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_G_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) hyp_wppgammaimagetceqndv_3 hyp_wppgammaimagetceqndv_4
  have p0001 :=
    @g_wppgammaminhwndv (syn_ctc C) k G dv_cache_0001 dv_cache_0002
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_simpl (.classMem (syn_cwppgamma G (syn_ctc C)) (syn_cwppcand G (syn_ctc C))) (syn_wral k (syn_cwppcand G (syn_ctc C)) (syn_wbr (syn_cwppgamma G (syn_ctc C)) (syn_clec) (.cv k)))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) hyp_wppgammaimagetceqndv_3 hyp_wppgammaimagetceqndv_4
  have p0006 :=
    @g_wppgammaminhwndv (syn_ctc C) k G dv_cache_0001 dv_cache_0002
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_simpr (.classMem (syn_cwppgamma G (syn_ctc C)) (syn_cwppcand G (syn_ctc C))) (syn_wral k (syn_cwppcand G (syn_ctc C)) (syn_wbr (syn_cwppgamma G (syn_ctc C)) (syn_clec) (.cv k)))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) hyp_wppgammaimagetceqndv_1 hyp_wppgammaimagetceqndv_2
  have p0011 :=
    @g_wppgammaminhwndv C d F dv_cache_0003 dv_cache_0004
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral d (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_eqid (syn_ctc (syn_cwppgamma F C))
  have p0016 :=
    @g_pm3_2i (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (syn_cwppgamma F C))) p0014 p0015
  have p0017 :=
    @g_tceq (.cv d) (syn_cwppgamma F C)
  have p0018 :=
    @g_eqeq2d (.classEq (.cv d) (syn_cwppgamma F C)) (syn_ctc (.cv d)) (syn_ctc (syn_cwppgamma F C)) (syn_ctc (syn_cwppgamma F C)) p0017
  have p0019 :=
    @g_rspcev (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d))) (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (syn_cwppgamma F C))) d (syn_cwppgamma F C) (syn_cwppcand F C) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0018
  have p0020 :=
    Nominal.mp p0016 p0019
  have p0021 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) hyp_wppgammaimagetceqndv_1 hyp_wppgammaimagetceqndv_2
  have p0022 :=
    @g_wppgammaminhwndv C d F dv_cache_0003 dv_cache_0004
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral d (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_elwppcand C (syn_cwppgamma F C) F
  have p0027 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)) (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))) p0026
  have p0028 :=
    Nominal.mp p0025 p0027
  have p0029 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)) (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_hwcardssnc (syn_cvv)
  have p0034 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma F C) p0033
  have p0035 :=
    Nominal.mp p0032 p0034
  have p0036 :=
    @g_tccl (syn_cwppgamma F C)
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_elex (syn_ctc (syn_cwppgamma F C)) (syn_cncs)
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_id (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C)))
  have p0041 :=
    @g_eleq1d (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C))) (.cv k) (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C)) p0040
  have p0042 :=
    @g_id (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C)))
  have p0043 :=
    @g_eqeq1d (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C))) (.cv k) (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d)) p0042
  have p0044 :=
    @g_rexbidv (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C))) (.classEq (.cv k) (syn_ctc (.cv d))) (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d))) d (syn_cwppcand F C) dv_cache_0008 p0043
  have p0045 :=
    @g_bibi12d (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C))) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (.classMem (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C))) (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wrex d (syn_cwppcand F C) (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d)))) p0041 p0044
  have p0046 :=
    @g_spcv (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d))))) (syn_wb (.classMem (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C))) (syn_wrex d (syn_cwppcand F C) (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d))))) k (syn_ctc (syn_cwppgamma F C)) dv_cache_0009 dv_cache_0010 p0039 p0045
  have p0047 :=
    Nominal.mp hyp_wppgammaimagetceqndv_5 p0046
  have p0048 :=
    @g_mpbir (.classMem (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C))) (syn_wrex d (syn_cwppcand F C) (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d)))) p0020 p0047
  have p0049 :=
    @g_sp (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d))))) k
  have p0050 :=
    Nominal.mp hyp_wppgammaimagetceqndv_5 p0049
  have p0051 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d)))) p0050
  have p0052 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0053 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) hyp_wppgammaimagetceqndv_1 hyp_wppgammaimagetceqndv_2
  have p0054 :=
    @g_wppgammaminhwndv C d F dv_cache_0003 dv_cache_0004
  have p0055 :=
    Nominal.mp p0053 p0054
  have p0056 :=
    @g_simpr (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral d (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)))
  have p0057 :=
    Nominal.mp p0055 p0056
  have p0058 :=
    @g_rsp (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)) d (syn_cwppcand F C)
  have p0059 :=
    Nominal.mp p0057 p0058
  have p0060 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cwppcand F C)) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)) p0052 p0059
  have p0061 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) hyp_wppgammaimagetceqndv_1 hyp_wppgammaimagetceqndv_2
  have p0062 :=
    @g_wppgammaminhwndv C d F dv_cache_0003 dv_cache_0004
  have p0063 :=
    Nominal.mp p0061 p0062
  have p0064 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral d (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)))
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_elwppcand C (syn_cwppgamma F C) F
  have p0067 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)) (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))) p0066
  have p0068 :=
    Nominal.mp p0065 p0067
  have p0069 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)) (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))
  have p0070 :=
    Nominal.mp p0068 p0069
  have p0071 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)
  have p0072 :=
    Nominal.mp p0070 p0071
  have p0073 :=
    @g_hwcardssnc (syn_cvv)
  have p0074 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma F C) p0073
  have p0075 :=
    Nominal.mp p0072 p0074
  have p0076 :=
    @g_a1i (.classMem (syn_cwppgamma F C) (syn_cncs)) (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) p0075
  have p0077 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0078 :=
    @g_elwppcand C (.cv d) F
  have p0079 :=
    @g_biimpi (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0078
  have p0080 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0077 p0079
  have p0081 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))
  have p0082 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) p0080 p0081
  have p0083 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0084 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0082 p0083
  have p0085 :=
    @g_hwcardssnc (syn_cvv)
  have p0086 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv d) p0085
  have p0087 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_chwcards (syn_cvv))) (.classMem (.cv d) (syn_cncs)) p0084 p0086
  have p0088 :=
    @g_jca (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (syn_cwppgamma F C) (syn_cncs)) (.classMem (.cv d) (syn_cncs)) p0076 p0087
  have p0089 :=
    @g_tlecg (syn_cwppgamma F C) (.cv d)
  have p0090 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (syn_cwppgamma F C) (syn_cncs)) (.classMem (.cv d) (syn_cncs))) (syn_wb (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)) (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (syn_ctc (.cv d)))) p0088 p0089
  have p0091 :=
    @g_mpbid (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)) (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (syn_ctc (.cv d))) p0060 p0090
  have p0092 :=
    @g_simpr (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0093 :=
    @g_breq2d (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.cv k) (syn_ctc (.cv d)) (syn_ctc (syn_cwppgamma F C)) (syn_clec) p0092
  have p0094 :=
    @g_mpbird (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k)) (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (syn_ctc (.cv d))) p0091 p0093
  have p0095 :=
    @g_rexlimiva (.classEq (.cv k) (syn_ctc (.cv d))) (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k)) d (syn_cwppcand F C) dv_cache_0011 p0094
  have p0096 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k)) p0051 p0095
  have p0097 :=
    @g_rgen (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k)) k (syn_cwppcand G (syn_ctc C)) p0096
  have p0098 :=
    @g_wppcandleastuniqclndv (syn_cwppgamma G (syn_ctc C)) (syn_ctc (syn_cwppgamma F C)) (syn_ctc C) k G dv_cache_0012 dv_cache_0009 dv_cache_0001 dv_cache_0002 p0004 p0009 p0048 p0097
  have p0099 :=
    @g_eqcomi (syn_cwppgamma G (syn_ctc C)) (syn_ctc (syn_cwppgamma F C)) p0098
  exact p0099

noncomputable def g_wppgammareachndv
    (C : Class) (F : Class) (hyp_wppgammareachndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wppgammareachndv_2 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classMem (syn_cwppgamma F C) (syn_cwppreach F C)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (h))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : k ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) hyp_wppgammareachndv_1 hyp_wppgammareachndv_2
  have p0001 :=
    @g_wppgammaminhwndv C k F dv_cache_0001 dv_cache_0002
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_elwppcand C (syn_cwppgamma F C) F
  have p0006 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)) (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))) p0005
  have p0007 :=
    Nominal.mp p0004 p0006
  have p0008 :=
    @g_simpr (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)) (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))
  have p0009 :=
    Nominal.mp p0007 p0008
  exact p0009

noncomputable def g_wpphitexvndv
    (C : Class) (F : Class) (I : Class) (hyp_wpphitexvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpphit F I C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ I.fv
  have p0000 :=
    (by simpa [syn_cwpphit] using (Nominal.classEqRefl (syn_cwpphit F I C)))
  have p0001 :=
    @g_a1i (.classEq (syn_cwpphit F I C) (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)))) (.classMem F (syn_cvv)) p0000
  have p0002 :=
    @g_eqid (syn_cfrec F I)
  have p0003 :=
    @g_frecexg (syn_cfrec F I) F I (syn_cvv) p0002
  have p0004 :=
    @g_cnvexg (syn_cfrec F I) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem F (syn_cvv)) (.classMem (syn_cfrec F I) (syn_cvv)) (.classMem (syn_ccnv (syn_cfrec F I)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_lecex
  have p0007 :=
    @g_snex C
  have p0008 :=
    @g_pm3_2i (.classMem (syn_clec) (syn_cvv)) (.classMem (syn_csn C) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_imaexg (syn_clec) (syn_csn C) (syn_cvv) (syn_cvv)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_a1i (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)) (.classMem F (syn_cvv)) p0010
  have p0012 :=
    @g_jca (.classMem F (syn_cvv)) (.classMem (syn_ccnv (syn_cfrec F I)) (syn_cvv)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)) p0005 p0011
  have p0013 :=
    @g_imaexg (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)) (syn_cvv) (syn_cvv)
  have p0014 :=
    @g_syl (.classMem F (syn_cvv)) (syn_wa (.classMem (syn_ccnv (syn_cfrec F I)) (syn_cvv)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))) (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_eqeltrd (.classMem F (syn_cvv)) (syn_cwpphit F I C) (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))) (syn_cvv) p0001 p0014
  have p0016 :=
    Nominal.mp hyp_wpphitexvndv_1 p0015
  exact p0016

noncomputable def g_elwpphitvndv
    (C : Class) (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wb (.classMem N (syn_cwpphit F I C)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N))))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ I.fv ∪ N.fv
  have p0000 :=
    (by simpa [syn_cwpphit] using (Nominal.classEqRefl (syn_cwpphit F I C)))
  have p0001 :=
    @g_eleq2i (syn_cwpphit F I C) (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))) N p0000
  have p0002 :=
    @g_a1i (syn_wb (.classMem N (syn_cwpphit F I C)) (.classMem N (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) p0001
  have p0003 :=
    @g_wpporbitfnndv F I
  have p0004 :=
    @g_elpreima (syn_cnnc) N (syn_cima (syn_clec) (syn_csn C)) (syn_cfrec F I)
  have p0005 :=
    @g_syl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wfn (syn_cfrec F I) (syn_cnnc)) (syn_wb (.classMem N (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)))) (syn_wa (.classMem N (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C))))) p0003 p0004
  have p0006 :=
    @g_elimasn (syn_clec) C (syn_cfv (syn_cfrec F I) N)
  have p0007 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N))))
  have p0008 :=
    @g_bicomi (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N)) (.classMem (syn_cop C (syn_cfv (syn_cfrec F I) N)) (syn_clec)) p0007
  have p0009 :=
    @g_bitri (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C))) (.classMem (syn_cop C (syn_cfv (syn_cfrec F I) N)) (syn_clec)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0006 p0008
  have p0010 :=
    @g_anbi2i (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N)) (.classMem N (syn_cnnc)) p0009
  have p0011 :=
    @g_a1i (syn_wb (syn_wa (.classMem N (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C)))) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N)))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) p0010
  have p0012 :=
    @g_bitrd (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)))) (syn_wa (.classMem N (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C)))) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N))) p0005 p0011
  have p0013 :=
    @g_bitrd (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cwpphit F I C)) (.classMem N (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)))) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N))) p0002 p0012
  exact p0013

noncomputable def g_wpphitminexvndv
    (x : Var) (C : Class) (S : Class) (m : Var) (n : Var) (F : Class) (I : Class) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (dv_I_x : x ∉ I.fv) (dv_S_m : m ∉ S.fv) (dv_S_n : n ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_m_n : m ≠ n) (dv_m_x : m ≠ x) (dv_n_x : n ≠ x) (hyp_wpphitminexvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr S (syn_cwe) (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C)))) (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m) (syn_cwpphit F I C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I C)) (syn_wbr (.cv m) S (.cv n))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ S.fv ∪ ({m} : Finset Var) ∪ ({n} : Finset Var) ∪ F.fv ∪ I.fv
  have dv_cache_0001 : x ∉ ((syn_cwpphit F I C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, dv_F_x, dv_I_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : m ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (.cv m) (syn_cwpphit F I C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_x), dv_C_x, dv_F_x, dv_I_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((syn_wa (syn_wbr S (syn_cwe) (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_m, dv_m_x, dv_C_m, dv_F_m, dv_I_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((syn_wa (syn_wbr S (syn_cwe) (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_n, dv_n_x, dv_C_n, dv_F_n, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((Wff.classMem (.cv x) (syn_cwpphit F I C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_m_x, dv_C_m, dv_F_m, dv_I_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((Wff.classMem (.cv x) (syn_cwpphit F I C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_n_x, dv_C_n, dv_F_n, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.classMem (.cv n) (syn_cwpphit F I C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_n_x), dv_C_x, dv_F_x, dv_I_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ m from (by exact Ne.symm dv_m_x))
  have dv_cache_0014 : x ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ n from (by exact Ne.symm dv_n_x))
  have dv_cache_0015 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show m ≠ n from (by exact dv_m_n))
  have p0000 :=
    @g_abid2 x (syn_cwpphit F I C) dv_cache_0001
  have p0001 :=
    @g_wpphitexvndv C F I hyp_wpphitminexvndv_1
  have p0002 :=
    @g_eqeltri (.cab x (.classMem (.cv x) (syn_cwpphit F I C))) (syn_cwpphit F I C) (syn_cvv) p0000 p0001
  have p0003 :=
    @g_eleq1 (.cv x) (.cv m) (syn_cwpphit F I C)
  have p0004 :=
    @g_eleq1 (.cv x) (.cv n) (syn_cwpphit F I C)
  have p0005 :=
    @g_simpl (syn_wbr S (syn_cwe) (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C)))
  have p0006 :=
    @g_simpr (syn_wbr S (syn_cwe) (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C)))
  have p0007_e01_recanon : Nominal.NPrf (.imp (.objEq x m) (syn_wb (.classMem (.cv x) (syn_cwpphit F I C)) (.classMem (.cv m) (syn_cwpphit F I C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0007_e02_recanon : Nominal.NPrf (.imp (.objEq x n) (syn_wb (.classMem (.cv x) (syn_cwpphit F I C)) (.classMem (.cv n) (syn_cwpphit F I C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0007 :=
    @g_weds (syn_wa (syn_wbr S (syn_cwe) (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C)))) (.classMem (.cv x) (syn_cwpphit F I C)) (.classMem (.cv m) (syn_cwpphit F I C)) (.classMem (.cv n) (syn_cwpphit F I C)) x m n (syn_cnnc) S dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0002 p0007_e01_recanon p0007_e02_recanon p0005 p0006
  exact p0007

noncomputable def g_elwpphitsucvndv
    (C : Class) (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wb (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I C)) (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ I.fv ∪ N.fv
  have p0000 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0001 :=
    @g_elwpphitvndv C F I (syn_cplc N (syn_c1c))
  have p0002 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wb (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I C)) (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c)))))) p0000 p0001
  have p0003 :=
    @g_wpporbitsucndv F I N
  have p0004 :=
    @g_breq2d (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) N)) C (syn_clec) p0003
  have p0005 :=
    @g_anbi2d (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c)))) (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) p0004
  have p0006 :=
    @g_bitrd (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I C)) (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c))))) (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))) p0002 p0005
  have p0007 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0008 :=
    @g_peano2 N
  have p0009 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.classMem N (syn_cnnc)) (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) p0007 p0008
  have p0010 :=
    @g_biantrurd (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) p0009
  have p0011 :=
    @g_bicomd (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))) p0010
  have p0012 :=
    @g_bitrd (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I C)) (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))) (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) p0006 p0011
  exact p0012

noncomputable def g_wpphitnestptndv
    (F : Class) (H : Class) (I : Class) (L : Class) (N : Class) (dv_F_N : Disjoint F.fv N.fv) (dv_I_N : Disjoint I.fv N.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.imp (.classMem N (syn_cwpphit F I H)) (.classMem N (syn_cwpphit F I L)))) := by
  let proofSupport : Finset Var := F.fv ∪ H.fv ∪ I.fv ∪ L.fv ∪ N.fv
  have p0000 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))
  have p0001 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.classMem N (syn_cnnc)) p0000 p0001
  have p0003 :=
    @g_a1d (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.classMem N (syn_cnnc)) (.classMem N (syn_cwpphit F I H)) p0002
  have p0004 :=
    @g_simpr (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))
  have p0005 :=
    @g_simpr (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)) (syn_wbr L (syn_clec) H) p0004 p0005
  have p0007 :=
    @g_a1d (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (syn_wbr L (syn_clec) H) (.classMem N (syn_cwpphit F I H)) p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))
  have p0009 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) p0008 p0009
  have p0011 :=
    @g_elwpphitvndv H F I N
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wb (.classMem N (syn_cwpphit F I H)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N)))) p0010 p0011
  have p0013 :=
    @g_biimpd (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.classMem N (syn_cwpphit F I H)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N))) p0012
  have p0014 :=
    @g_simpr (.classMem N (syn_cnnc)) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N))
  have p0015 :=
    @g_syl6 (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.classMem N (syn_cwpphit F I H)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N))) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0013 p0014
  have p0016 :=
    @g_jcad (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.classMem N (syn_cwpphit F I H)) (syn_wbr L (syn_clec) H) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0007 p0015
  have p0017 :=
    @g_simpr (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))
  have p0018 :=
    @g_simpl (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) p0017 p0018
  have p0020 :=
    @g_lectr L H (syn_cfv (syn_cfrec F I) N)
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (.imp (syn_wa (syn_wbr L (syn_clec) H) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))) p0019 p0020
  have p0022 :=
    @g_syld (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.classMem N (syn_cwpphit F I H)) (syn_wa (syn_wbr L (syn_clec) H) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0016 p0021
  have p0023 :=
    @g_jcad (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.classMem N (syn_cwpphit F I H)) (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0003 p0022
  have p0024 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))
  have p0025 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) p0024 p0025
  have p0027 :=
    @g_elwpphitvndv L F I N
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wb (.classMem N (syn_cwpphit F I L)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)))) p0026 p0027
  have p0029 :=
    @g_biimprd (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.classMem N (syn_cwpphit F I L)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))) p0028
  have p0030 :=
    @g_syld (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.classMem N (syn_cwpphit F I H)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))) (.classMem N (syn_cwpphit F I L)) p0023 p0029
  exact p0030

#print axioms g_wpphitnestptndv

end NFChoice.DirectNominalPrf.WPPReplay
