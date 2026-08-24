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
import NominalWPPReplayChunk013Compact001Part014

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

noncomputable def g_clos1ex
    (R : Class) (S : Class) (hyp_clos1ex_1 : Nominal.NPrf (.classMem S (syn_cvv))) (hyp_clos1ex_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cclos1 S R) (syn_cvv)) := by
  let proofSupport : Finset Var := R.fv ∪ S.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : a ∉ (R).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (S).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((syn_csset)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((syn_cimage R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ ((syn_cima R (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((syn_wss (syn_cima R (.cv a)) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ ((syn_cin (syn_cima (syn_csset) (syn_csn S)) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfix, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elin (.cv a) (syn_cima (syn_csset) (syn_csn S)) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R)))
  have p0002 :=
    @g_elimasn (syn_csset) S (.cv a)
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr S (syn_csset) (.cv a))))
  have p0004 :=
    @g_vex a
  have p0005 :=
    @g_brsset S (.cv a) hyp_clos1ex_1 p0004
  have p0006 :=
    @g_n_3bitr2i (.classMem (.cv a) (syn_cima (syn_csset) (syn_csn S))) (.classMem (syn_cop S (.cv a)) (syn_csset)) (syn_wbr S (syn_csset) (.cv a)) (syn_wss S (.cv a)) p0002 p0003 p0005
  have p0007 :=
    @g_elfix (.cv a) (syn_ccom (syn_csset) (syn_cimage R))
  have p0008 :=
    @g_brco b (.cv a) (.cv a) (syn_csset) (syn_cimage R) dv_cache_0003 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    @g_vex b
  have p0010 :=
    @g_brimage (.cv a) (.cv b) R p0004 p0009
  have p0011 :=
    @g_anbi1i (syn_wbr (.cv a) (syn_cimage R) (.cv b)) (.classEq (.cv b) (syn_cima R (.cv a))) (syn_wbr (.cv b) (syn_csset) (.cv a)) p0010
  have p0012 :=
    @g_exbii (syn_wa (syn_wbr (.cv a) (syn_cimage R) (.cv b)) (syn_wbr (.cv b) (syn_csset) (.cv a))) (syn_wa (.classEq (.cv b) (syn_cima R (.cv a))) (syn_wbr (.cv b) (syn_csset) (.cv a))) b p0011
  have p0013 :=
    @g_imaex R (.cv a) hyp_clos1ex_2 p0004
  have p0014 :=
    @g_breq1 (.cv b) (syn_cima R (.cv a)) (.cv a) (syn_csset)
  have p0015 :=
    @g_brsset (syn_cima R (.cv a)) (.cv a) p0013 p0004
  have p0016 :=
    @g_syl6bb (.classEq (.cv b) (syn_cima R (.cv a))) (syn_wbr (.cv b) (syn_csset) (.cv a)) (syn_wbr (syn_cima R (.cv a)) (syn_csset) (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)) p0014 p0015
  have p0017 :=
    @g_ceqsexv (syn_wbr (.cv b) (syn_csset) (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)) b (syn_cima R (.cv a)) dv_cache_0006 dv_cache_0007 p0013 p0016
  have p0018 :=
    @g_bitri (syn_wex b (syn_wa (syn_wbr (.cv a) (syn_cimage R) (.cv b)) (syn_wbr (.cv b) (syn_csset) (.cv a)))) (syn_wex b (syn_wa (.classEq (.cv b) (syn_cima R (.cv a))) (syn_wbr (.cv b) (syn_csset) (.cv a)))) (syn_wss (syn_cima R (.cv a)) (.cv a)) p0012 p0017
  have p0019 :=
    @g_bitri (syn_wbr (.cv a) (syn_ccom (syn_csset) (syn_cimage R)) (.cv a)) (syn_wex b (syn_wa (syn_wbr (.cv a) (syn_cimage R) (.cv b)) (syn_wbr (.cv b) (syn_csset) (.cv a)))) (syn_wss (syn_cima R (.cv a)) (.cv a)) p0008 p0018
  have p0020 :=
    @g_bitri (.classMem (.cv a) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R)))) (syn_wbr (.cv a) (syn_ccom (syn_csset) (syn_cimage R)) (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)) p0007 p0019
  have p0021 :=
    @g_anbi12i (.classMem (.cv a) (syn_cima (syn_csset) (syn_csn S))) (syn_wss S (.cv a)) (.classMem (.cv a) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R)))) (syn_wss (syn_cima R (.cv a)) (.cv a)) p0006 p0020
  have p0022 :=
    @g_bitri (.classMem (.cv a) (syn_cin (syn_cima (syn_csset) (syn_csn S)) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))))) (syn_wa (.classMem (.cv a) (syn_cima (syn_csset) (syn_csn S))) (.classMem (.cv a) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))))) (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) p0001 p0021
  have p0023 :=
    @g_eqabi (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) a (syn_cin (syn_cima (syn_csset) (syn_csn S)) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R)))) dv_cache_0008 p0022
  have p0024 :=
    @g_ssetex
  have p0025 :=
    @g_snex S
  have p0026 :=
    @g_imaex (syn_csset) (syn_csn S) p0024 p0025
  have p0027 :=
    @g_ssetex
  have p0028 :=
    @g_imageex R hyp_clos1ex_2
  have p0029 :=
    @g_coex (syn_csset) (syn_cimage R) p0027 p0028
  have p0030 :=
    @g_fixex (syn_ccom (syn_csset) (syn_cimage R)) p0029
  have p0031 :=
    @g_inex (syn_cima (syn_csset) (syn_csn S)) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))) p0026 p0030
  have p0032 :=
    @g_eqeltrri (syn_cin (syn_cima (syn_csset) (syn_csn S)) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R)))) (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))) (syn_cvv) p0023 p0031
  have p0033 :=
    @g_intex (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))) p0032
  have p0034 :=
    @g_eqeltri (syn_cclos1 S R) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_cvv) p0000 p0033
  exact p0034

noncomputable def g_clos1exg
    (R : Class) (S : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem S V) (.classMem R W)) (.classMem (syn_cclos1 S R) (syn_cvv))) := by
  let proofSupport : Finset Var := R.fv ∪ S.fv ∪ V.fv ∪ W.fv
  let s : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_s_not_S : s ∉ S.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_not_V : s ∉ V.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_not_W : s ∉ W.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_V : r ∉ V.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_W : r ∉ W.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_s_ne_r : s ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_s : r ≠ s :=
    Ne.symm fresh_s_ne_r
  have dv_cache_0001 : s ∉ (S).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (S).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((Wff.classMem (syn_cclos1 S R) (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : s ∉ ((Wff.classMem (syn_cclos1 S (.cv r)) (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_r, fresh_s_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_clos1eq1 (.cv r) (.cv s) S
  have p0001 :=
    @g_eleq1d (.classEq (.cv s) S) (syn_cclos1 (.cv s) (.cv r)) (syn_cclos1 S (.cv r)) (syn_cvv) p0000
  have p0002 :=
    @g_clos1eq2 (.cv r) S R
  have p0003 :=
    @g_eleq1d (.classEq (.cv r) R) (syn_cclos1 S (.cv r)) (syn_cclos1 S R) (syn_cvv) p0002
  have p0004 :=
    @g_vex s
  have p0005 :=
    @g_vex r
  have p0006 :=
    @g_clos1ex (.cv r) (.cv s) p0004 p0005
  have p0007 :=
    @g_vtocl2g (.classMem (syn_cclos1 (.cv s) (.cv r)) (syn_cvv)) (.classMem (syn_cclos1 S (.cv r)) (syn_cvv)) (.classMem (syn_cclos1 S R) (syn_cvv)) s r S R V W dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0001 p0003 p0006
  exact p0007

noncomputable def g_clos1base
    (C : Class) (R : Class) (S : Class) (hyp_clos1base_1 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) :
    Nominal.NPrf (syn_wss S C) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv ∪ S.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : a ∉ (S).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ssmin (syn_wss (syn_cima R (.cv a)) (.cv a)) a S dv_cache_0001
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a dv_cache_0002 dv_cache_0001
  have p0002 :=
    @g_eqtr2i C (syn_cclos1 S R) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) hyp_clos1base_1 p0001
  have p0003 :=
    @g_sseqtri S (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) C p0000 p0002
  exact p0003

noncomputable def g_clos1conn
    (A : Class) (B : Class) (C : Class) (R : Class) (S : Class) (hyp_clos1base_1 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem B C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_a_ne_z : a ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wbr (.cv x) R (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((syn_wbr (.cv x) R (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Wff.imp (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem B C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_C, fresh_y_not_B, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Wff.imp (syn_wa (.classMem A C) (syn_wbr A R (.cv y))) (.classMem (.cv y) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_C, fresh_x_ne_y, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex A B R
  have p0001 :=
    @g_adantl (syn_wbr A R B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem A C) p0000
  have p0002 :=
    @g_eleq1 (.cv x) A C
  have p0003 :=
    @g_breq1 (.cv x) A (.cv y) R
  have p0004 :=
    @g_anbi12d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C) (syn_wbr (.cv x) R (.cv y)) (syn_wbr A R (.cv y)) p0002 p0003
  have p0005 :=
    @g_imbi1d (.classEq (.cv x) A) (syn_wa (.classMem (.cv x) C) (syn_wbr (.cv x) R (.cv y))) (syn_wa (.classMem A C) (syn_wbr A R (.cv y))) (.classMem (.cv y) C) p0004
  have p0006 :=
    @g_breq2 (.cv y) B A R
  have p0007 :=
    @g_anbi2d (.classEq (.cv y) B) (syn_wbr A R (.cv y)) (syn_wbr A R B) (.classMem A C) p0006
  have p0008 :=
    @g_eleq1 (.cv y) B C
  have p0009 :=
    @g_imbi12d (.classEq (.cv y) B) (syn_wa (.classMem A C) (syn_wbr A R (.cv y))) (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem (.cv y) C) (.classMem B C) p0007 p0008
  have p0010 :=
    @g_breq1 (.cv z) (.cv x) (.cv y) R
  have p0011 :=
    @g_rspcev (syn_wbr (.cv z) R (.cv y)) (syn_wbr (.cv x) R (.cv y)) z (.cv x) (.cv a) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0010
  have p0012 :=
    @g_elima z (.cv y) R (.cv a) dv_cache_0004 dv_cache_0005 dv_cache_0002
  have p0013_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objMem x a) (syn_wbr (.cv x) R (.cv y))) (syn_wrex z (.cv a) (syn_wbr (.cv z) R (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0011
  have p0013 :=
    @g_sylibr (syn_wa (.objMem x a) (syn_wbr (.cv x) R (.cv y))) (syn_wrex z (.cv a) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cima R (.cv a))) p0013_e00_recanon p0012
  have p0014 :=
    @g_ancoms (.objMem x a) (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv y) (syn_cima R (.cv a))) p0013
  have p0015 :=
    @g_ssel (syn_cima R (.cv a)) (.cv a) (.cv y)
  have p0016_e01_recanon : Nominal.NPrf (.imp (syn_wss (syn_cima R (.cv a)) (.cv a)) (.imp (.classMem (.cv y) (syn_cima R (.cv a))) (.objMem y a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cima syn_wrex syn_wex syn_wbr syn_cop syn_cun
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0015
  have p0016 :=
    @g_syl5 (syn_wa (syn_wbr (.cv x) R (.cv y)) (.objMem x a)) (.classMem (.cv y) (syn_cima R (.cv a))) (syn_wss (syn_cima R (.cv a)) (.cv a)) (.objMem y a) p0014 p0016_e01_recanon
  have p0017 :=
    @g_exp3a (syn_wss (syn_cima R (.cv a)) (.cv a)) (syn_wbr (.cv x) R (.cv y)) (.objMem x a) (.objMem y a) p0016
  have p0018 :=
    @g_com12 (syn_wss (syn_cima R (.cv a)) (.cv a)) (syn_wbr (.cv x) R (.cv y)) (.imp (.objMem x a) (.objMem y a)) p0017
  have p0019 :=
    @g_adantld (syn_wbr (.cv x) R (.cv y)) (syn_wss (syn_cima R (.cv a)) (.cv a)) (.imp (.objMem x a) (.objMem y a)) (syn_wss S (.cv a)) p0018
  have p0020 :=
    @g_a2d (syn_wbr (.cv x) R (.cv y)) (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem x a) (.objMem y a) p0019
  have p0021 :=
    @g_alimdv (syn_wbr (.cv x) R (.cv y)) (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem x a)) (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem y a)) a dv_cache_0006 p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a dv_cache_0007 dv_cache_0008
  have p0023 :=
    @g_eqtri C (syn_cclos1 S R) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) hyp_clos1base_1 p0022
  have p0024 :=
    @g_eleq2i C (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (.cv x) p0023
  have p0025 :=
    @g_vex x
  have p0026 :=
    @g_elintab (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) a (.cv x) dv_cache_0009 p0025
  have p0027_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))) (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem x a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0026
  have p0027 :=
    @g_bitri (.classMem (.cv x) C) (.classMem (.cv x) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))) (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem x a))) p0024 p0027_e01_recanon
  have p0028 :=
    @g_eleq2i C (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (.cv y) p0023
  have p0029 :=
    @g_vex y
  have p0030 :=
    @g_elintab (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) a (.cv y) dv_cache_0010 p0029
  have p0031_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))) (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem y a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0030
  have p0031 :=
    @g_bitri (.classMem (.cv y) C) (.classMem (.cv y) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))) (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem y a))) p0028 p0031_e01_recanon
  have p0032 :=
    @g_n_3imtr4g (syn_wbr (.cv x) R (.cv y)) (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem x a))) (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem y a))) (.classMem (.cv x) C) (.classMem (.cv y) C) p0021 p0027 p0031
  have p0033 :=
    @g_impcom (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) C) (.classMem (.cv y) C) p0032
  have p0034 :=
    @g_vtocl2g (.imp (syn_wa (.classMem (.cv x) C) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv y) C)) (.imp (syn_wa (.classMem A C) (syn_wbr A R (.cv y))) (.classMem (.cv y) C)) (.imp (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem B C)) x y A B (syn_cvv) (syn_cvv) dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0005 p0009 p0033
  have p0035 :=
    @g_mpcom (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem B C) p0001 p0034
  exact p0035

#print axioms g_clos1conn

end NFChoice.DirectNominalPrf.WPPReplay
