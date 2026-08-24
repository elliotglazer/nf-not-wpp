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
import NominalWPPReplayChunk015Compact001Part016

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

noncomputable def g_frectchom0
    (x : Var) (F : Class) (G : Class) (I : Class) (N : Class) (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) (dv_I_x : x ∉ I.fv) (hyp_frectchom0_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_frectchom0_2 : Nominal.NPrf (.classMem I (syn_cdm F))) (hyp_frectchom0_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_frectchom0_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_frectchom0_5 : Nominal.NPrf (.classMem (syn_ctc I) (syn_cdm G))) (hyp_frectchom0_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_frectchom0_7 : Nominal.NPrf (syn_wral x (syn_cdm F) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x)))))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) N)) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc N)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_I : n ∉ I.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_ne_x : m ≠ x := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_m : x ≠ m :=
    Ne.symm fresh_m_ne_x
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_m_not_G : m ∉ G.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_not_I : m ∉ I.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have dv_cache_0001 : n ∉ ((syn_cfrecteq F G I)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cfv (syn_cfrec F I) (.cv m))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_m, dv_F_x, dv_I_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cdm F)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_m, dv_F_x, dv_I_x, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.classMem (.cv m) (syn_cfrecteq F G I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((Wff.classMem (.cv n) (syn_cfrecteq F G I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, fresh_m_not_F, fresh_m_not_G, fresh_m_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((Wff.classMem (syn_c0c) (syn_cfrecteq F G I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ ((Wff.classMem N (syn_cfrecteq F G I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((Wff.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : n ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have p0000 :=
    @g_elex F (syn_cfuns)
  have p0001 :=
    Nominal.mp hyp_frectchom0_1 p0000
  have p0002 :=
    @g_elex G (syn_cfuns)
  have p0003 :=
    Nominal.mp hyp_frectchom0_4 p0002
  have p0004 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem G (syn_cvv)) p0001 p0003
  have p0005 :=
    @g_frecteqex F G I
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_abid2 n (syn_cfrecteq F G I) dv_cache_0001
  have p0008 :=
    @g_eleq1i (.cab n (.classMem (.cv n) (syn_cfrecteq F G I))) (syn_cfrecteq F G I) (syn_cvv) p0007
  have p0009 :=
    @g_mpbir (.classMem (.cab n (.classMem (.cv n) (syn_cfrecteq F G I))) (syn_cvv)) (.classMem (syn_cfrecteq F G I) (syn_cvv)) p0006 p0008
  have p0010 :=
    @g_id (.classEq (.cv n) (syn_c0c))
  have p0011 :=
    @g_eleq1d (.classEq (.cv n) (syn_c0c)) (.cv n) (syn_c0c) (syn_cfrecteq F G I) p0010
  have p0012 :=
    @g_id (.classEq (.cv n) (.cv m))
  have p0013 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (syn_cfrecteq F G I) p0012
  have p0014 :=
    @g_id (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
  have p0015 :=
    @g_eleq1d (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I) p0014
  have p0016 :=
    @g_id (.classEq (.cv n) N)
  have p0017 :=
    @g_eleq1d (.classEq (.cv n) N) (.cv n) N (syn_cfrecteq F G I) p0016
  have p0018 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
  have p0019 :=
    @g_eqid (syn_cfrec F I)
  have p0020 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0021 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0022 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0023 :=
    @g_frec0 (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0019 p0020 p0021 p0022
  have p0024 :=
    Nominal.mp p0018 p0023
  have p0025 :=
    @g_tceq (syn_cfv (syn_cfrec F I) (syn_c0c)) I
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_tc0c
  have p0028 :=
    @g_fveq2i (syn_ctc (syn_c0c)) (syn_c0c) (syn_cfrec G (syn_ctc I)) p0027
  have p0029 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0030 :=
    @g_eqid (syn_cfrec G (syn_ctc I))
  have p0031 :=
    @g_simp1 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))
  have p0032 :=
    @g_simp2 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))
  have p0033 :=
    @g_simp3 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))
  have p0034 :=
    @g_frec0 (syn_w3a (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))) (syn_cfrec G (syn_ctc I)) G (syn_ctc I) p0030 p0031 p0032 p0033
  have p0035 :=
    Nominal.mp p0029 p0034
  have p0036 :=
    @g_eqtri (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_c0c))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_c0c)) (syn_ctc I) p0028 p0035
  have p0037 :=
    @g_eqcomi (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_c0c))) (syn_ctc I) p0036
  have p0038 :=
    @g_eqtri (syn_ctc (syn_cfv (syn_cfrec F I) (syn_c0c))) (syn_ctc I) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_c0c))) p0026 p0037
  have p0039 :=
    @g_peano1
  have p0040 :=
    @g_frecteqvalcl (syn_c0c) F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3 hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_c0c))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_c0c)))) p0038 p0041
  have p0043 :=
    @g_eqid (syn_cfrec F I)
  have p0044 :=
    @g_a1i (.classMem F (syn_cfuns)) (.classMem (.cv m) (syn_cnnc)) hyp_frectchom0_1
  have p0045 :=
    @g_a1i (.classMem I (syn_cdm F)) (.classMem (.cv m) (syn_cnnc)) hyp_frectchom0_2
  have p0046 :=
    @g_a1i (syn_wss (syn_crn F) (syn_cdm F)) (.classMem (.cv m) (syn_cnnc)) hyp_frectchom0_3
  have p0047 :=
    @g_id (.classMem (.cv m) (syn_cnnc))
  have p0048 :=
    @g_frecsuc (.classMem (.cv m) (syn_cnnc)) (syn_cfrec F I) F I (.cv m) p0043 p0044 p0045 p0046 p0047
  have p0049 :=
    @g_adantr (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) p0048
  have p0050 :=
    @g_tceq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))
  have p0051 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))) (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))) p0049 p0050
  have p0052 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3
  have p0053 :=
    @g_frecdomfv F I (.cv m)
  have p0054 :=
    @g_mpan (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cdm F)) p0052 p0053
  have p0055 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)))
  have p0056 :=
    @g_fveq2d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)))) (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)) F p0055
  have p0057 :=
    @g_tceq (syn_cfv F (.cv x)) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))
  have p0058 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)))) (.classEq (syn_cfv F (.cv x)) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))) p0056 p0057
  have p0059 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)))
  have p0060 :=
    @g_tceq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m))
  have p0061 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)))) (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m))) (.classEq (syn_ctc (.cv x)) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))) p0059 p0060
  have p0062 :=
    @g_fveq2d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_ctc (.cv x)) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) G p0061
  have p0063 :=
    @g_eqeq12d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (.cv x) (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_ctc (syn_cfv F (.cv x))) (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_cfv G (syn_ctc (.cv x))) (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))) p0058 p0062
  have p0064 :=
    @g_rspcdv (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x)))) (.classEq (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))))) x (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cdm F) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0054 p0063
  have p0065 :=
    @g_mpi (.classMem (.cv m) (syn_cnnc)) (syn_wral x (syn_cdm F) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x))))) (.classEq (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))))) hyp_frectchom0_7 p0064
  have p0066 :=
    @g_adantr (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))))) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) p0065
  have p0067 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))) (syn_ctc (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))) p0051 p0066
  have p0068 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))
  have p0069 :=
    @g_fveq2d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))) G p0068
  have p0070 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv G (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) p0067 p0069
  have p0071 :=
    @g_eqid (syn_cfrec G (syn_ctc I))
  have p0072 :=
    @g_a1i (.classMem G (syn_cfuns)) (.classMem (.cv m) (syn_cnnc)) hyp_frectchom0_4
  have p0073 :=
    @g_a1i (.classMem (syn_ctc I) (syn_cdm G)) (.classMem (.cv m) (syn_cnnc)) hyp_frectchom0_5
  have p0074 :=
    @g_a1i (syn_wss (syn_crn G) (syn_cdm G)) (.classMem (.cv m) (syn_cnnc)) hyp_frectchom0_6
  have p0075 :=
    @g_id (.classMem (.cv m) (syn_cnnc))
  have p0076 :=
    @g_nntccl (.cv m)
  have p0077 :=
    @g_syl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0075 p0076
  have p0078 :=
    @g_frecsuc (.classMem (.cv m) (syn_cnnc)) (syn_cfrec G (syn_ctc I)) G (syn_ctc I) (syn_ctc (.cv m)) p0071 p0072 p0073 p0074 p0077
  have p0079 :=
    @g_adantr (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) p0078
  have p0080 :=
    @g_eqcomd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) p0079
  have p0081 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) p0070 p0080
  have p0082 :=
    @g_id (.classMem (.cv m) (syn_cnnc))
  have p0083 :=
    @g_nnnc (.cv m)
  have p0084 :=
    @g_syl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cncs)) p0082 p0083
  have p0085 :=
    @g_n_1cnc
  have p0086 :=
    @g_a1i (.classMem (syn_c1c) (syn_cncs)) (.classMem (.cv m) (syn_cnnc)) p0085
  have p0087 :=
    @g_jca (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cncs)) (.classMem (syn_c1c) (syn_cncs)) p0084 p0086
  have p0088 :=
    @g_tcdi (.cv m) (syn_c1c)
  have p0089 :=
    @g_syl (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cncs)) (.classMem (syn_c1c) (syn_cncs))) (.classEq (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_ctc (syn_c1c)))) p0087 p0088
  have p0090 :=
    @g_tc1c
  have p0091 :=
    @g_a1i (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) (.classMem (.cv m) (syn_cnnc)) p0090
  have p0092 :=
    @g_addceq2d (.classMem (.cv m) (syn_cnnc)) (syn_ctc (syn_c1c)) (syn_c1c) (syn_ctc (.cv m)) p0091
  have p0093 :=
    @g_eqtrd (.classMem (.cv m) (syn_cnnc)) (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_ctc (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)) p0089 p0092
  have p0094 :=
    @g_adantr (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) p0093
  have p0095 :=
    @g_fveq2d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)) (syn_cfrec G (syn_ctc I)) p0094
  have p0096 :=
    @g_eqcomd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) p0095
  have p0097 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m))))) (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) p0081 p0096
  have p0098 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) p0097
  have p0099 :=
    @g_frecteqval m F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3 hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0100 :=
    @g_bicomd (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) p0099
  have p0101 :=
    @g_id (.classMem (.cv m) (syn_cnnc))
  have p0102 :=
    @g_peano2 (.cv m)
  have p0103 :=
    @g_syl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) p0101 p0102
  have p0104 :=
    @g_frecteqvalcl (syn_cplc (.cv m) (syn_c1c)) F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3 hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0105 :=
    @g_syl (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (syn_wb (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))))) p0103 p0104
  have p0106 :=
    @g_bicomd (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) p0105
  have p0107 :=
    @g_n_3imtr3d (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv m)))) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (syn_cplc (.cv m) (syn_c1c))))) (.classMem (.cv m) (syn_cfrecteq F G I)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I)) p0098 p0100 p0106
  have p0108_e02_recanon : Nominal.NPrf (.imp (.objEq n m) (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I)) (.classMem (.cv m) (syn_cfrecteq F G I)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfrecteq syn_cuni1 syn_cuni syn_wex syn_wa syn_cin syn_ccompl syn_cnin syn_wnan syn_c1c syn_cfix syn_crn syn_cima syn_wrex syn_wbr syn_cop syn_cun syn_cvv syn_ccom syn_copab syn_ccnv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0013
  have p0108 :=
    @g_finds (.classMem (.cv n) (syn_cfrecteq F G I)) (.classMem (syn_c0c) (syn_cfrecteq F G I)) (.classMem (.cv m) (syn_cfrecteq F G I)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cfrecteq F G I)) (.classMem N (syn_cfrecteq F G I)) n m N dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0009 p0011 p0108_e02_recanon p0015 p0017 p0042 p0107
  have p0109 :=
    @g_frecteqvalcl N F G I hyp_frectchom0_1 hyp_frectchom0_2 hyp_frectchom0_3 hyp_frectchom0_4 hyp_frectchom0_5 hyp_frectchom0_6
  have p0110 :=
    @g_mpbid (.classMem N (syn_cnnc)) (.classMem N (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) N)) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc N))) p0108 p0109
  exact p0110

noncomputable def g_f1pwexd
    (ph : Wff) (A : Class) (B : Class) (g : Var) (F : Class) (dv_A_g : g ∉ A.fv) (dv_B_g : g ∉ B.fv) (dv_F_g : g ∉ F.fv) (dv_g_ph : g ∉ ph.fv) (hyp_f1pwexd_1 : Nominal.NPrf (.imp ph (.classMem F (syn_cvv)))) (hyp_f1pwexd_2 : Nominal.NPrf (.imp ph (syn_wf1 F A B))) :
    Nominal.NPrf (.imp ph (syn_wex g (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ ({g} : Finset Var) ∪ F.fv
  have dv_cache_0001 : g ∉ ((syn_cpw A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : g ∉ ((syn_cpw (syn_crn F))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_g_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_f1f1orn A B F
  have p0001 :=
    @g_syl ph (syn_wf1 F A B) (syn_wf1o F A (syn_crn F)) hyp_f1pwexd_2 p0000
  have p0002 :=
    @g_jca ph (.classMem F (syn_cvv)) (syn_wf1o F A (syn_crn F)) hyp_f1pwexd_1 p0001
  have p0003 :=
    @g_f1oeng A (syn_crn F) (syn_cvv) F
  have p0004 :=
    @g_syl ph (syn_wa (.classMem F (syn_cvv)) (syn_wf1o F A (syn_crn F))) (syn_wbr A (syn_cen) (syn_crn F)) p0002 p0003
  have p0005 :=
    @g_enpw A (syn_crn F)
  have p0006 :=
    @g_syl ph (syn_wbr A (syn_cen) (syn_crn F)) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (syn_crn F))) p0004 p0005
  have p0007 :=
    @g_bren (syn_cpw A) (syn_cpw (syn_crn F)) g dv_cache_0001 dv_cache_0002
  have p0008 :=
    @g_biimpi (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (syn_crn F))) (syn_wex g (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))) p0007
  have p0009 :=
    @g_syl ph (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (syn_crn F))) (syn_wex g (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))) p0006 p0008
  have p0010 :=
    @g_f1of1 (syn_cpw A) (syn_cpw (syn_crn F)) (.cv g)
  have p0011 :=
    @g_a1i (.imp (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))) (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))) ph p0010
  have p0012 :=
    @g_f1f A B F
  have p0013 :=
    @g_syl ph (syn_wf1 F A B) (syn_wf F A B) hyp_f1pwexd_2 p0012
  have p0014 :=
    @g_frn A B F
  have p0015 :=
    @g_syl ph (syn_wf F A B) (syn_wss (syn_crn F) B) p0013 p0014
  have p0016 :=
    @g_sspwb (syn_crn F) B
  have p0017 :=
    @g_biimpi (syn_wss (syn_crn F) B) (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B)) p0016
  have p0018 :=
    @g_syl ph (syn_wss (syn_crn F) B) (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B)) p0015 p0017
  have p0019 :=
    @g_a1d ph (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B)) (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))) p0018
  have p0020 :=
    @g_jcad ph (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))) (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))) (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B)) p0011 p0019
  have p0021 :=
    @g_f1ss (syn_cpw A) (syn_cpw (syn_crn F)) (syn_cpw B) (.cv g)
  have p0022 :=
    @g_syl6 ph (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))) (syn_wa (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))) (syn_wss (syn_cpw (syn_crn F)) (syn_cpw B))) (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) p0020 p0021
  have p0023 :=
    @g_eximdv ph (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F))) (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) g dv_cache_0003 p0022
  have p0024 :=
    @g_mpd ph (syn_wex g (syn_wf1o (.cv g) (syn_cpw A) (syn_cpw (syn_crn F)))) (syn_wex g (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B))) p0009 p0023
  exact p0024

noncomputable def g_f1pwpwexd
    (ph : Wff) (A : Class) (B : Class) (h : Var) (F : Class) (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) (hyp_f1pwpwexd_1 : Nominal.NPrf (.imp ph (.classMem F (syn_cvv)))) (hyp_f1pwpwexd_2 : Nominal.NPrf (.imp ph (syn_wf1 F A B))) :
    Nominal.NPrf (.imp ph (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ ({h} : Finset Var) ∪ F.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_ph : g ∉ ph.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_ne_h : g ≠ h := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_g : h ≠ g :=
    Ne.symm fresh_g_ne_h
  have fresh_g_not_F : g ∉ F.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have dv_cache_0001 : g ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : g ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : h ∉ ((syn_cpw A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : h ∉ ((syn_cpw B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : h ∉ ((Class.cv g)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : h ∉ ((syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, dv_B_h, fresh_h_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : g ∉ ((syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, fresh_g_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_f1pwexd ph A B g F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_f1pwpwexd_1 hyp_f1pwpwexd_2
  have p0001 :=
    @g_vex g
  have p0002 :=
    @g_a1i (.classMem (.cv g) (syn_cvv)) (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) p0001
  have p0003 :=
    @g_id (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B))
  have p0004 :=
    @g_f1pwexd (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) (syn_cpw A) (syn_cpw B) h (.cv g) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0002 p0003
  have p0005 :=
    @g_a1i (.imp (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))) ph p0004
  have p0006 :=
    @g_exlimdv ph (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B)) (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) g dv_cache_0009 dv_cache_0004 p0005
  have p0007 :=
    @g_mpd ph (syn_wex g (syn_wf1 (.cv g) (syn_cpw A) (syn_cpw B))) (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) p0000 p0006
  exact p0007

noncomputable def g_f1pw2exim
    (A : Class) (B : Class) (f : Var) (h : Var) (dv_A_f : f ∉ A.fv) (dv_A_h : h ∉ A.fv) (dv_B_f : f ∉ B.fv) (dv_B_h : h ∉ B.fv) (dv_f_h : f ≠ h) :
    Nominal.NPrf (.imp (syn_wex f (syn_wf1 (.cv f) A B)) (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({f} : Finset Var) ∪ ({h} : Finset Var)
  have dv_cache_0001 : h ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, dv_B_f, dv_f_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex f
  have p0001 :=
    @g_a1i (.classMem (.cv f) (syn_cvv)) (syn_wf1 (.cv f) A B) p0000
  have p0002 :=
    @g_id (syn_wf1 (.cv f) A B)
  have p0003 :=
    @g_f1pwpwexd (syn_wf1 (.cv f) A B) A B h (.cv f) dv_cache_0001 dv_cache_0002 p0001 p0002
  have p0004 :=
    @g_exlimiv (syn_wf1 (.cv f) A B) (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) f dv_cache_0003 p0003
  exact p0004

noncomputable def g_ncpw2le
    (A : Class) (B : Class) (hyp_ncpw2le_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_ncpw2le_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wbr (syn_cnc (syn_cpw (syn_cpw A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw B))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let h : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (h))
  have fresh_h_not_B : h ∉ B.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_h_ne_f : h ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_h : f ≠ h :=
    Ne.symm fresh_h_ne_f
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : h ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ≠ h := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ h from (by exact fresh_f_ne_h))
  have dv_cache_0006 : h ∉ ((syn_cpw (syn_cpw A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : h ∉ ((syn_cpw (syn_cpw B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nclenc A B f dv_cache_0001 dv_cache_0002 hyp_ncpw2le_1 hyp_ncpw2le_2
  have p0001 :=
    @g_biimpi (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wex f (syn_wf1 (.cv f) A B)) p0000
  have p0002 :=
    @g_f1pw2exim A B f h dv_cache_0001 dv_cache_0003 dv_cache_0002 dv_cache_0004 dv_cache_0005
  have p0003 :=
    @g_syl (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wex f (syn_wf1 (.cv f) A B)) (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) p0001 p0002
  have p0004 :=
    @g_pwex A hyp_ncpw2le_1
  have p0005 :=
    @g_pwex (syn_cpw A) p0004
  have p0006 :=
    @g_pwex B hyp_ncpw2le_2
  have p0007 :=
    @g_pwex (syn_cpw B) p0006
  have p0008 :=
    @g_nclenc (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)) h dv_cache_0006 dv_cache_0007 p0005 p0007
  have p0009 :=
    @g_biimpri (syn_wbr (syn_cnc (syn_cpw (syn_cpw A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw B)))) (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) p0008
  have p0010 :=
    @g_syl (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wex h (syn_wf1 (.cv h) (syn_cpw (syn_cpw A)) (syn_cpw (syn_cpw B)))) (syn_wbr (syn_cnc (syn_cpw (syn_cpw A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw B)))) p0003 p0009
  exact p0010

noncomputable def g_hwnisobaseext
    (v : Var) (u : Var) (A : Class) (D : Class) (dv_u_v : u ≠ v) (hyp_hwnisobaseext_1 : Nominal.NPrf (syn_wss D A)) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (.imp (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ D.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_v : h ≠ v := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_h : v ≠ h :=
    Ne.symm fresh_h_ne_v
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_h : u ≠ h :=
    Ne.symm fresh_h_ne_u
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ≠ v := by
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0002 : h ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0004 : h ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0005 : h ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hwcnssbase A D hyp_hwnisobaseext_1
  have p0001 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))
  have p0002 :=
    @g_sseldi (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_chwcn D) (syn_chwcn A) (.cv u) p0000 p0001
  have p0003 :=
    @g_hwcnssbase A D hyp_hwnisobaseext_1
  have p0004 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))
  have p0005 :=
    @g_sseldi (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_chwcn D) (syn_chwcn A) (.cv v) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0002 p0005
  have p0007 :=
    @g_adantr (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) p0006
  have p0008 :=
    @g_hwcnssbase A D hyp_hwnisobaseext_1
  have p0009 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))
  have p0010 :=
    @g_sseldi (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_chwcn D) (syn_chwcn A) (.cv u) p0008 p0009
  have p0011 :=
    @g_hwcnraw u A
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) p0010 p0011
  have p0013 :=
    @g_hwcnssbase A D hyp_hwnisobaseext_1
  have p0014 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))
  have p0015 :=
    @g_sseldi (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_chwcn D) (syn_chwcn A) (.cv v) p0013 p0014
  have p0016 :=
    @g_hwcnraw v A
  have p0017 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcodes A)) p0015 p0016
  have p0018 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)) p0012 p0017
  have p0019 :=
    @g_adantr (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) p0018
  have p0020 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v))
  have p0021 :=
    @g_hwnisohwisob v u D dv_cache_0001
  have p0022 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwiso D) (.cv v))) p0021
  have p0023 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwiso D) (.cv v)) p0022
  have p0024 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) (syn_wbr (.cv u) (syn_chwiso D) (.cv v)) p0020 p0023
  have p0025 :=
    @g_brhwisoany v u D h dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0026 :=
    @g_sylib (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v))) (syn_wbr (.cv u) (syn_chwiso D) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0024 p0025
  have p0027 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0026
  have p0028 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0019 p0027
  have p0029 :=
    @g_brhwisoany v u A h dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0030 :=
    @g_sylibr (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0028 p0029
  have p0031 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0007 p0030
  have p0032 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0033 :=
    @g_sylibr (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0031 p0032
  have p0034 :=
    @g_ex (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0033
  exact p0034

#print axioms g_hwnisobaseext

end NFChoice.DirectNominalPrf.WPPReplay
