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
import NominalWPPReplayChunk013Compact001Part004

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

noncomputable def g_fnsex
     :
    Nominal.NPrf (.classMem (syn_cfns) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let f : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_ne_a : f ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_f : a ≠ f :=
    Ne.symm fresh_f_ne_a
  have dv_cache_0001 : a ≠ f := by
    exact (show a ≠ f from (by exact fresh_a_ne_f))
  have dv_cache_0002 : f ∉ ((syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ a from (by exact fresh_f_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fns f a dv_cache_0001
  have p0001 :=
    @g_vex a
  have p0002 :=
    @g_opelxp (.cv f) (.cv a) (syn_cfuns) (syn_cvv)
  have p0003 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv))) (.classMem (.cv f) (syn_cfuns)) (.classMem (.cv a) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_vex f
  have p0005 :=
    @g_elfuns (.cv f) p0004
  have p0006 :=
    @g_bitri (.classMem (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv))) (.classMem (.cv f) (syn_cfuns)) (syn_wfun (.cv f)) p0003 p0005
  have p0007 :=
    @g_eqcom (syn_cima (syn_c1st) (.cv f)) (.cv a)
  have p0008 :=
    @g_dfdm4 (.cv f)
  have p0009 :=
    @g_eqeq1i (syn_cdm (.cv f)) (syn_cima (syn_c1st) (.cv f)) (.cv a) p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cimage (syn_c1st)) (.cv a))))
  have p0011 :=
    @g_brimage (.cv f) (.cv a) (syn_c1st) p0004 p0001
  have p0012 :=
    @g_bitr3i (.classMem (syn_cop (.cv f) (.cv a)) (syn_cimage (syn_c1st))) (syn_wbr (.cv f) (syn_cimage (syn_c1st)) (.cv a)) (.classEq (.cv a) (syn_cima (syn_c1st) (.cv f))) p0010 p0011
  have p0013 :=
    @g_n_3bitr4ri (.classEq (syn_cima (syn_c1st) (.cv f)) (.cv a)) (.classEq (.cv a) (syn_cima (syn_c1st) (.cv f))) (.classEq (syn_cdm (.cv f)) (.cv a)) (.classMem (syn_cop (.cv f) (.cv a)) (syn_cimage (syn_c1st))) p0007 p0009 p0012
  have p0014 :=
    @g_anbi12i (.classMem (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv))) (syn_wfun (.cv f)) (.classMem (syn_cop (.cv f) (.cv a)) (syn_cimage (syn_c1st))) (.classEq (syn_cdm (.cv f)) (.cv a)) p0006 p0013
  have p0015 :=
    @g_elin (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st))
  have p0016 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (.cv f) (.cv a))))
  have p0017 :=
    @g_n_3bitr4i (syn_wa (.classMem (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv a)) (syn_cimage (syn_c1st)))) (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) (.cv a))) (.classMem (syn_cop (.cv f) (.cv a)) (syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st)))) (syn_wfn (.cv f) (.cv a)) p0014 p0015 p0016
  have p0018 :=
    @g_opabbi2i (syn_wfn (.cv f) (.cv a)) f a (syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st))) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0017
  have p0019 :=
    @g_eqtr4i (syn_cfns) (syn_copab f a (syn_wfn (.cv f) (.cv a))) (syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st))) p0000 p0018
  have p0020 :=
    @g_funsex
  have p0021 :=
    @g_vvex
  have p0022 :=
    @g_xpex (syn_cfuns) (syn_cvv) p0020 p0021
  have p0023 :=
    @g_n_1stex
  have p0024 :=
    @g_imageex (syn_c1st) p0023
  have p0025 :=
    @g_inex (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st)) p0022 p0024
  have p0026 :=
    @g_eqeltri (syn_cfns) (syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st))) (syn_cvv) p0019 p0025
  exact p0026

noncomputable def g_brfns
    (A : Class) (F : Class) (hyp_brfns_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr F (syn_cfns) A) (syn_wfn F A)) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let a : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_f : a ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_a : f ≠ a :=
    Ne.symm fresh_a_ne_f
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_f_ne_b : f ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_f : b ≠ f :=
    Ne.symm fresh_f_ne_b
  have dv_cache_0001 : b ≠ f := by
    exact (show b ≠ f from (by exact fresh_b_ne_f))
  have dv_cache_0002 : f ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : f ∉ ((syn_wfn F (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, fresh_f_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((syn_wfn F (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_F, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : f ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show f ≠ b from (by exact fresh_f_ne_b))
  have dv_cache_0009 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_wbr F (syn_cfns) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_F, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_wfn F A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_F, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex F A (syn_cfns)
  have p0001 :=
    @g_simprd (syn_wbr F (syn_cfns) A) (.classMem F (syn_cvv)) (.classMem A (syn_cvv)) p0000
  have p0002 :=
    @g_fndm A F
  have p0003 :=
    @g_eqcomd (syn_wfn F A) (syn_cdm F) A p0002
  have p0004 :=
    @g_dmexg F (syn_cvv)
  have p0005 :=
    Nominal.mp hyp_brfns_1 p0004
  have p0006 :=
    @g_syl6eqel (syn_wfn F A) A (syn_cdm F) (syn_cvv) p0003 p0005
  have p0007 :=
    @g_breq2 (.cv a) A F (syn_cfns)
  have p0008 :=
    @g_fneq2 (.cv a) A F
  have p0009 :=
    @g_vex a
  have p0010 :=
    @g_fneq1 (.cv b) (.cv f) F
  have p0011 :=
    @g_fneq2 (.cv b) (.cv a) F
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fns f b dv_cache_0001
  have p0013 :=
    @g_brab (syn_wfn (.cv f) (.cv b)) (syn_wfn F (.cv b)) (syn_wfn F (.cv a)) f b F (.cv a) (syn_cfns) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 hyp_brfns_1 p0009 p0010 p0011 p0012
  have p0014 :=
    @g_vtoclbg (syn_wbr F (syn_cfns) (.cv a)) (syn_wfn F (.cv a)) (syn_wbr F (syn_cfns) A) (syn_wfn F A) a A (syn_cvv) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0007 p0008 p0013
  have p0015 :=
    @g_pm5_21nii (syn_wbr F (syn_cfns) A) (.classMem A (syn_cvv)) (syn_wfn F A) p0001 p0006 p0014
  exact p0015

noncomputable def g_pprodeq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpprod C A) (syn_cpprod C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_coeq1 A B (syn_c2nd)
  have p0001 :=
    @g_txpeq2 (syn_ccom A (syn_c2nd)) (syn_ccom B (syn_c2nd)) (syn_ccom C (syn_c1st))
  have p0002 :=
    @g_syl (.classEq A B) (.classEq (syn_ccom A (syn_c2nd)) (syn_ccom B (syn_c2nd))) (.classEq (syn_ctxp (syn_ccom C (syn_c1st)) (syn_ccom A (syn_c2nd))) (syn_ctxp (syn_ccom C (syn_c1st)) (syn_ccom B (syn_c2nd)))) p0000 p0001
  have p0003 :=
    (by simpa [syn_cpprod] using (Nominal.classEqRefl (syn_cpprod C A)))
  have p0004 :=
    (by simpa [syn_cpprod] using (Nominal.classEqRefl (syn_cpprod C B)))
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B) (syn_ctxp (syn_ccom C (syn_c1st)) (syn_ccom A (syn_c2nd))) (syn_ctxp (syn_ccom C (syn_c1st)) (syn_ccom B (syn_c2nd))) (syn_cpprod C A) (syn_cpprod C B) p0002 p0003 p0004
  exact p0005

noncomputable def g_qrpprod
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr B S D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_D : x ∉ D.fv := by
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
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_S : w ∉ S.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_w_ne_a : w ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_w : a ≠ w :=
    Ne.symm fresh_w_ne_a
  have dv_cache_0001 : a ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((syn_wbr (.cv x) R (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_z, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_c2nd)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_wbr (.cv y) S (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_w, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_C, fresh_w_not_D, fresh_w_not_R, fresh_w_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C (.cv w))) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_C, fresh_z_ne_w, fresh_z_not_R, fresh_z_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((Wff.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr B S D))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, fresh_y_not_D, fresh_y_not_A, fresh_y_not_B, fresh_y_not_R, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((Wff.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_D, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_R, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex (syn_cop A B) (syn_cop C D) (syn_cpprod R S)
  have p0001 :=
    @g_opexb A B
  have p0002 :=
    @g_opexb C D
  have p0003 :=
    @g_anbi12i (.classMem (syn_cop A B) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_cop C D) (syn_cvv)) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0001 p0002
  have p0004 :=
    @g_sylib (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D)) (syn_wa (.classMem (syn_cop A B) (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))) p0000 p0003
  have p0005 :=
    @g_brex A C R
  have p0006 :=
    @g_brex B D S
  have p0007 :=
    @g_anim12i (syn_wbr A R C) (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv))) (syn_wbr B S D) (syn_wa (.classMem B (syn_cvv)) (.classMem D (syn_cvv))) p0005 p0006
  have p0008 :=
    @g_an4 (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
  have p0009 :=
    @g_sylibr (syn_wa (syn_wbr A R C) (syn_wbr B S D)) (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (.classMem B (syn_cvv)) (.classMem D (syn_cvv)))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))) p0007 p0008
  have p0010 :=
    @g_opeq1 (.cv x) A (.cv y)
  have p0011 :=
    @g_breq1d (.classEq (.cv x) A) (syn_cop (.cv x) (.cv y)) (syn_cop A (.cv y)) (syn_cop C D) (syn_cpprod R S) p0010
  have p0012 :=
    @g_breq1 (.cv x) A C R
  have p0013 :=
    @g_anbi1d (.classEq (.cv x) A) (syn_wbr (.cv x) R C) (syn_wbr A R C) (syn_wbr (.cv y) S D) p0012
  have p0014 :=
    @g_bibi12d (.classEq (.cv x) A) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D)) (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D)) p0011 p0013
  have p0015 :=
    @g_imbi2d (.classEq (.cv x) A) (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D))) (syn_wb (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0014
  have p0016 :=
    @g_opeq2 (.cv y) B A
  have p0017 :=
    @g_breq1d (.classEq (.cv y) B) (syn_cop A (.cv y)) (syn_cop A B) (syn_cop C D) (syn_cpprod R S) p0016
  have p0018 :=
    @g_breq1 (.cv y) B D S
  have p0019 :=
    @g_anbi2d (.classEq (.cv y) B) (syn_wbr (.cv y) S D) (syn_wbr B S D) (syn_wbr A R C) p0018
  have p0020 :=
    @g_bibi12d (.classEq (.cv y) B) (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D)) (syn_wa (syn_wbr A R C) (syn_wbr B S D)) p0017 p0019
  have p0021 :=
    @g_imbi2d (.classEq (.cv y) B) (syn_wb (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D))) (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr B S D))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0020
  have p0022 :=
    @g_opeq1 (.cv z) C (.cv w)
  have p0023 :=
    @g_breq2d (.classEq (.cv z) C) (syn_cop (.cv z) (.cv w)) (syn_cop C (.cv w)) (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) p0022
  have p0024 :=
    @g_breq2 (.cv z) C (.cv x) R
  have p0025 :=
    @g_anbi1d (.classEq (.cv z) C) (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S (.cv w)) p0024
  have p0026 :=
    @g_bibi12d (.classEq (.cv z) C) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop (.cv z) (.cv w))) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S (.cv w))) p0023 p0025
  have p0027 :=
    @g_opeq2 (.cv w) D C
  have p0028 :=
    @g_breq2d (.classEq (.cv w) D) (syn_cop C (.cv w)) (syn_cop C D) (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) p0027
  have p0029 :=
    @g_breq2 (.cv w) D (.cv y) S
  have p0030 :=
    @g_anbi2d (.classEq (.cv w) D) (syn_wbr (.cv y) S (.cv w)) (syn_wbr (.cv y) S D) (syn_wbr (.cv x) R C) p0029
  have p0031 :=
    @g_bibi12d (.classEq (.cv w) D) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C (.cv w))) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S (.cv w))) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D)) p0028 p0030
  have p0032 :=
    (by simpa [syn_cpprod] using (Nominal.classEqRefl (syn_cpprod R S)))
  have p0033 :=
    @g_breqi (syn_cop (.cv x) (.cv y)) (syn_cop (.cv z) (.cv w)) (syn_cpprod R S) (syn_ctxp (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd))) p0032
  have p0034 :=
    @g_trtxp (syn_cop (.cv x) (.cv y)) (.cv z) (.cv w) (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd))
  have p0035 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop (.cv z) (.cv w))) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ctxp (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd))) (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w))) p0033 p0034
  have p0036 :=
    @g_brco a (syn_cop (.cv x) (.cv y)) (.cv z) R (syn_c1st) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0037 :=
    @g_vex x
  have p0038 :=
    @g_vex y
  have p0039 :=
    @g_opbr1st (.cv x) (.cv y) (.cv a) p0037 p0038
  have p0040 :=
    @g_eqcom (.cv x) (.cv a)
  have p0041_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a)) (.objEq x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_c1st syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0039
  have p0041_e01_recanon : Nominal.NPrf (syn_wb (.objEq x a) (.objEq a x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0040
  have p0041 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a)) (.objEq x a) (.objEq a x) p0041_e00_recanon p0041_e01_recanon
  have p0042 :=
    @g_anbi1i (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a)) (.objEq a x) (syn_wbr (.cv a) R (.cv z)) p0041
  have p0043 :=
    @g_exbii (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a)) (syn_wbr (.cv a) R (.cv z))) (syn_wa (.objEq a x) (syn_wbr (.cv a) R (.cv z))) a p0042
  have p0044 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z)) (syn_wex a (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a)) (syn_wbr (.cv a) R (.cv z)))) (syn_wex a (syn_wa (.objEq a x) (syn_wbr (.cv a) R (.cv z)))) p0036 p0043
  have p0045 :=
    @g_breq1 (.cv a) (.cv x) (.cv z) R
  have p0046 :=
    @g_ceqsexv (syn_wbr (.cv a) R (.cv z)) (syn_wbr (.cv x) R (.cv z)) a (.cv x) dv_cache_0005 dv_cache_0006 p0037 p0045
  have p0047_e01_recanon : Nominal.NPrf (syn_wb (syn_wex a (syn_wa (.objEq a x) (syn_wbr (.cv a) R (.cv z)))) (syn_wbr (.cv x) R (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0046
  have p0047 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z)) (syn_wex a (syn_wa (.objEq a x) (syn_wbr (.cv a) R (.cv z)))) (syn_wbr (.cv x) R (.cv z)) p0044 p0047_e01_recanon
  have p0048 :=
    @g_brco a (syn_cop (.cv x) (.cv y)) (.cv w) S (syn_c2nd) dv_cache_0001 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0049 :=
    @g_opbr2nd (.cv x) (.cv y) (.cv a) p0037 p0038
  have p0050 :=
    @g_eqcom (.cv y) (.cv a)
  have p0051_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a)) (.objEq y a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_c2nd syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0049
  have p0051_e01_recanon : Nominal.NPrf (syn_wb (.objEq y a) (.objEq a y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0050
  have p0051 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a)) (.objEq y a) (.objEq a y) p0051_e00_recanon p0051_e01_recanon
  have p0052 :=
    @g_anbi1i (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a)) (.objEq a y) (syn_wbr (.cv a) S (.cv w)) p0051
  have p0053 :=
    @g_exbii (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a)) (syn_wbr (.cv a) S (.cv w))) (syn_wa (.objEq a y) (syn_wbr (.cv a) S (.cv w))) a p0052
  have p0054 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w)) (syn_wex a (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a)) (syn_wbr (.cv a) S (.cv w)))) (syn_wex a (syn_wa (.objEq a y) (syn_wbr (.cv a) S (.cv w)))) p0048 p0053
  have p0055 :=
    @g_breq1 (.cv a) (.cv y) (.cv w) S
  have p0056 :=
    @g_ceqsexv (syn_wbr (.cv a) S (.cv w)) (syn_wbr (.cv y) S (.cv w)) a (.cv y) dv_cache_0010 dv_cache_0011 p0038 p0055
  have p0057_e01_recanon : Nominal.NPrf (syn_wb (syn_wex a (syn_wa (.objEq a y) (syn_wbr (.cv a) S (.cv w)))) (syn_wbr (.cv y) S (.cv w))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0056
  have p0057 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w)) (syn_wex a (syn_wa (.objEq a y) (syn_wbr (.cv a) S (.cv w)))) (syn_wbr (.cv y) S (.cv w)) p0054 p0057_e01_recanon
  have p0058 :=
    @g_anbi12i (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr (.cv x) R (.cv z)) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w)) (syn_wbr (.cv y) S (.cv w)) p0047 p0057
  have p0059 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))) p0035 p0058
  have p0060 :=
    @g_vtocl2g (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))) (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C (.cv w))) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S (.cv w)))) (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D))) z w C D (syn_cvv) (syn_cvv) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 p0026 p0031 p0059
  have p0061 :=
    @g_vtocl2g (.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D)))) (.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D)))) (.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr B S D)))) x y A B (syn_cvv) (syn_cvv) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0015 p0021 p0060
  have p0062 :=
    @g_imp (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wbr A R C) (syn_wbr B S D))) p0061
  have p0063 :=
    @g_pm5_21nii (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D)) (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))) (syn_wa (syn_wbr A R C) (syn_wbr B S D)) p0004 p0009 p0062
  exact p0063

noncomputable def g_pprodexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cpprod A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    (by simpa [syn_cpprod] using (Nominal.classEqRefl (syn_cpprod A B)))
  have p0001 :=
    @g_n_1stex
  have p0002 :=
    @g_coexg A (syn_c1st) V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem A V) (.classMem (syn_c1st) (syn_cvv)) (.classMem (syn_ccom A (syn_c1st)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_n_2ndex
  have p0005 :=
    @g_coexg B (syn_c2nd) W (syn_cvv)
  have p0006 :=
    @g_mpan2 (.classMem B W) (.classMem (syn_c2nd) (syn_cvv)) (.classMem (syn_ccom B (syn_c2nd)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_txpexg (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd)) (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl2an (.classMem A V) (.classMem (syn_ccom A (syn_c1st)) (syn_cvv)) (.classMem (syn_ccom B (syn_c2nd)) (syn_cvv)) (.classMem (syn_ctxp (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd))) (syn_cvv)) (.classMem B W) p0003 p0006 p0007
  have p0009 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cpprod A B) (syn_ctxp (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd))) (syn_cvv) p0000 p0008
  exact p0009

noncomputable def g_pprodex
    (A : Class) (B : Class) (hyp_pprodex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_pprodex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cpprod A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_pprodexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cpprod A B) (syn_cvv)) hyp_pprodex_1 hyp_pprodex_2 p0000
  exact p0001

#print axioms g_pprodex

end NFChoice.DirectNominalPrf.WPPReplay
