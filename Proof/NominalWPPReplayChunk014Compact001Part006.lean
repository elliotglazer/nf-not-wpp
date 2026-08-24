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
import NominalWPPReplayChunk014Compact001Part005

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

noncomputable def g_frec0
    (ph : Wff) (F : Class) (G : Class) (I : Class) (hyp_frec0_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) (hyp_frec0_2 : Nominal.NPrf (.imp ph (.classMem G (syn_cfuns)))) (hyp_frec0_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G)))) (hyp_frec0_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cfv F (syn_c0c)) I)) := by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_I : y ∉ I.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (G).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (I).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cop (syn_c0c) I)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_peano1
  have p0001 :=
    @g_opexg (syn_c0c) I (syn_cnnc) (syn_cdm G)
  have p0002 :=
    @g_sylancr ph (.classMem (syn_c0c) (syn_cnnc)) (.classMem I (syn_cdm G)) (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) p0000 hyp_frec0_3 p0001
  have p0003 :=
    @g_snidg (syn_cop (syn_c0c) I) (syn_cvv)
  have p0004 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) p0002 p0003
  have p0005 :=
    @g_orcd ph (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex y F (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_cop (syn_c0c) I))) p0004
  have p0006 :=
    @g_snex (syn_cop (syn_c0c) I)
  have p0007 :=
    @g_csucex x
  have p0008 :=
    @g_pprodexg (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G (syn_cvv) (syn_cfuns)
  have p0009 :=
    @g_sylancr ph (.classMem (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (syn_cvv)) (.classMem G (syn_cfuns)) (.classMem (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_cvv)) p0007 hyp_frec0_2 p0008
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x G I dv_cache_0001 dv_cache_0002
  have p0011 :=
    @g_eqtri F (syn_cfrec G I) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) hyp_frec0_1 p0010
  have p0012 :=
    @g_clos1basesucg y (syn_cop (syn_c0c) I) F (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0011
  have p0013 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv)) (.classMem (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_cvv)) (syn_wb (.classMem (syn_cop (syn_c0c) I) F) (syn_wo (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex y F (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_cop (syn_c0c) I))))) p0006 p0009 p0012
  have p0014 :=
    @g_mpbird ph (.classMem (syn_cop (syn_c0c) I) F) (syn_wo (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex y F (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_cop (syn_c0c) I)))) p0005 p0013
  have p0015 :=
    @g_fnfrec ph F G I hyp_frec0_1 hyp_frec0_2 hyp_frec0_3 hyp_frec0_4
  have p0016 :=
    @g_peano1
  have p0017 :=
    @g_fnopfvb (syn_cnnc) (syn_c0c) I F
  have p0018 :=
    @g_sylancl ph (syn_wfn F (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc)) (syn_wb (.classEq (syn_cfv F (syn_c0c)) I) (.classMem (syn_cop (syn_c0c) I) F)) p0015 p0016 p0017
  have p0019 :=
    @g_mpbird ph (.classEq (syn_cfv F (syn_c0c)) I) (.classMem (syn_cop (syn_c0c) I) F) p0014 p0018
  exact p0019

noncomputable def g_frecsuc
    (ph : Wff) (F : Class) (G : Class) (I : Class) (X : Class) (hyp_frecsuc_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) (hyp_frecsuc_2 : Nominal.NPrf (.imp ph (.classMem G (syn_cfuns)))) (hyp_frecsuc_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G)))) (hyp_frecsuc_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) (hyp_frecsuc_5 : Nominal.NPrf (.imp ph (.classMem X (syn_cnnc)))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cfv F (syn_cplc X (syn_c1c))) (syn_cfv G (syn_cfv F X)))) := by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv ∪ X.fv
  let y : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_I : y ∉ I.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_w_not_F : w ∉ F.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_G : w ∉ G.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_I : w ∉ I.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_X : w ∉ X.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have dv_cache_0001 : y ∉ ((syn_cplc (.cv w) (syn_c1c))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ≠ y := by
    clear dv_cache_0001
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0003 : w ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_cplc X (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cplc X (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : w ∉ ((Wff.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cop X (syn_cfv F X))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_wa (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c))) (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, fresh_y_ne_w, fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ (I).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fnfrec ph F G I hyp_frecsuc_1 hyp_frecsuc_2 hyp_frecsuc_3 hyp_frecsuc_4
  have p0001 :=
    @g_fnfun (syn_cnnc) F
  have p0002 :=
    @g_syl ph (syn_wfn F (syn_cnnc)) (syn_wfun F) p0000 p0001
  have p0003 :=
    @g_dmfrec ph F G I (syn_cfuns) hyp_frecsuc_1 hyp_frecsuc_2 hyp_frecsuc_3 hyp_frecsuc_4
  have p0004 :=
    @g_eleqtrrd ph X (syn_cnnc) (syn_cdm F) hyp_frecsuc_5 p0003
  have p0005 :=
    @g_funfvop X F
  have p0006 :=
    @g_syl2anc ph (syn_wfun F) (.classMem X (syn_cdm F)) (.classMem (syn_cop X (syn_cfv F X)) F) p0002 p0004 p0005
  have p0007 :=
    @g_eqid (syn_cplc X (syn_c1c))
  have p0008 :=
    @g_peano2 X
  have p0009 :=
    @g_syl ph (.classMem X (syn_cnnc)) (.classMem (syn_cplc X (syn_c1c)) (syn_cnnc)) hyp_frecsuc_5 p0008
  have p0010 :=
    @g_addceq1 (.cv w) X (syn_c1c)
  have p0011 :=
    @g_eqeq2d (.classEq (.cv w) X) (syn_cplc (.cv w) (syn_c1c)) (syn_cplc X (syn_c1c)) (.cv y) p0010
  have p0012 :=
    @g_eqeq1 (.cv y) (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c))
  have p0013 :=
    @g_mptv w y (syn_cplc (.cv w) (syn_c1c)) dv_cache_0001 dv_cache_0002
  have p0014 :=
    @g_brabg (.classEq (.cv y) (syn_cplc (.cv w) (syn_c1c))) (.classEq (.cv y) (syn_cplc X (syn_c1c))) (.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c))) w y X (syn_cplc X (syn_c1c)) (syn_cnnc) (syn_cnnc) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0002 p0011 p0012 p0013
  have p0015 :=
    @g_syl2anc ph (.classMem X (syn_cnnc)) (.classMem (syn_cplc X (syn_c1c)) (syn_cnnc)) (syn_wb (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c))) (.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c)))) hyp_frecsuc_5 p0009 p0014
  have p0016 :=
    @g_mpbiri ph (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c))) (.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c))) p0007 p0015
  have p0017 :=
    @g_elfunsi G
  have p0018 :=
    @g_syl ph (.classMem G (syn_cfuns)) (syn_wfun G) hyp_frecsuc_2 p0017
  have p0019 :=
    @g_snssd ph I (syn_cdm G) hyp_frecsuc_3
  have p0020 :=
    @g_unssd ph (syn_crn G) (syn_csn I) (syn_cdm G) hyp_frecsuc_4 p0019
  have p0021 :=
    @g_frecxpg F G I (syn_cfuns) hyp_frecsuc_1
  have p0022 :=
    @g_syl ph (.classMem G (syn_cfuns)) (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) hyp_frecsuc_2 p0021
  have p0023 :=
    @g_rnss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))
  have p0024 :=
    @g_syl ph (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) (syn_wss (syn_crn F) (syn_crn (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))) p0022 p0023
  have p0025 :=
    @g_rnxpss (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))
  have p0026 :=
    @g_syl6ss ph (syn_crn F) (syn_crn (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) (syn_cun (syn_crn G) (syn_csn I)) p0024 p0025
  have p0027 :=
    @g_fvelrn X F
  have p0028 :=
    @g_syl2anc ph (syn_wfun F) (.classMem X (syn_cdm F)) (.classMem (syn_cfv F X) (syn_crn F)) p0002 p0004 p0027
  have p0029 :=
    @g_sseldd ph (syn_crn F) (syn_cun (syn_crn G) (syn_csn I)) (syn_cfv F X) p0026 p0028
  have p0030 :=
    @g_sseldd ph (syn_cun (syn_crn G) (syn_csn I)) (syn_cdm G) (syn_cfv F X) p0020 p0029
  have p0031 :=
    @g_funfvop (syn_cfv F X) G
  have p0032 :=
    @g_syl2anc ph (syn_wfun G) (.classMem (syn_cfv F X) (syn_cdm G)) (.classMem (syn_cop (syn_cfv F X) (syn_cfv G (syn_cfv F X))) G) p0018 p0030 p0031
  have p0033 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X)))))
  have p0034 :=
    @g_sylibr ph (.classMem (syn_cop (syn_cfv F X) (syn_cfv G (syn_cfv F X))) G) (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X))) p0032 p0033
  have p0035 :=
    @g_breq1 (.cv y) (syn_cop X (syn_cfv F X)) (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
  have p0036 :=
    @g_qrpprod X (syn_cfv F X) (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0037 :=
    @g_syl6bb (.classEq (.cv y) (syn_cop X (syn_cfv F X))) (syn_wbr (.cv y) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))) (syn_wbr (syn_cop X (syn_cfv F X)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))) (syn_wa (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c))) (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X)))) p0035 p0036
  have p0038 :=
    @g_rspcev (syn_wbr (.cv y) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))) (syn_wa (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c))) (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X)))) y (syn_cop X (syn_cfv F X)) F dv_cache_0009 dv_cache_0010 dv_cache_0011 p0037
  have p0039 :=
    @g_syl12anc ph (.classMem (syn_cop X (syn_cfv F X)) F) (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c))) (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X))) (syn_wrex y F (syn_wbr (.cv y) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))))) p0006 p0016 p0034 p0038
  have p0040 :=
    @g_olcd ph (syn_wrex y F (syn_wbr (.cv y) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))))) (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) (syn_csn (syn_cop (syn_c0c) I))) p0039
  have p0041 :=
    @g_snex (syn_cop (syn_c0c) I)
  have p0042 :=
    @g_csucex w
  have p0043 :=
    @g_pprodexg (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G (syn_cvv) (syn_cfuns)
  have p0044 :=
    @g_sylancr ph (.classMem (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv)) (.classMem G (syn_cfuns)) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) p0042 hyp_frecsuc_2 p0043
  have p0045 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec w G I dv_cache_0012 dv_cache_0013
  have p0046 :=
    @g_eqtri F (syn_cfrec G I) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)) hyp_frecsuc_1 p0045
  have p0047 :=
    @g_clos1basesucg y (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0014 dv_cache_0010 dv_cache_0015 dv_cache_0016 p0046
  have p0048 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv)) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) (syn_wb (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F) (syn_wo (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex y F (syn_wbr (.cv y) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))))))) p0041 p0044 p0047
  have p0049 :=
    @g_mpbird ph (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F) (syn_wo (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex y F (syn_wbr (.cv y) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))))) p0040 p0048
  have p0050 :=
    @g_fnopfvb (syn_cnnc) (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)) F
  have p0051 :=
    @g_syl2anc ph (syn_wfn F (syn_cnnc)) (.classMem (syn_cplc X (syn_c1c)) (syn_cnnc)) (syn_wb (.classEq (syn_cfv F (syn_cplc X (syn_c1c))) (syn_cfv G (syn_cfv F X))) (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F)) p0000 p0009 p0050
  have p0052 :=
    @g_mpbird ph (.classEq (syn_cfv F (syn_cplc X (syn_c1c))) (syn_cfv G (syn_cfv F X))) (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F) p0049 p0051
  exact p0052

noncomputable def g_wppcg
    (A : Class) (B : Class) (f : Var) (g : Var) (h : Var) (V : Class) (W : Class) (dv_A_V : Disjoint A.fv V.fv) (dv_A_W : Disjoint A.fv W.fv) (dv_A_f : f ∉ A.fv) (dv_A_g : g ∉ A.fv) (dv_A_h : h ∉ A.fv) (dv_B_V : Disjoint B.fv V.fv) (dv_B_W : Disjoint B.fv W.fv) (dv_B_f : f ∉ B.fv) (dv_B_g : g ∉ B.fv) (dv_B_h : h ∉ B.fv) (dv_V_W : Disjoint V.fv W.fv) (dv_f_g : f ≠ g) (dv_f_h : f ≠ h) (dv_g_h : g ≠ h) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.imp (syn_wwpp) (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A))) (syn_wex h (syn_wf1 (.cv h) A B))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({f} : Finset Var) ∪ ({g} : Finset Var) ∪ ({h} : Finset Var) ∪ V.fv ∪ W.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_y : g ≠ y :=
    Ne.symm fresh_y_ne_g
  have fresh_y_ne_h : y ≠ h := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_h_ne_y : h ≠ y :=
    Ne.symm fresh_y_ne_h
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_ne_g : x ≠ g := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_x : g ≠ x :=
    Ne.symm fresh_x_ne_g
  have fresh_x_ne_h : x ≠ h := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_h_ne_x : h ≠ x :=
    Ne.symm fresh_x_ne_h
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : f ≠ g := by
    exact (show f ≠ g from (by exact dv_f_g))
  have dv_cache_0002 : f ≠ h := by
    clear dv_cache_0001
    exact (show f ≠ h from (by exact dv_f_h))
  have dv_cache_0003 : f ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0004 : f ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0005 : g ≠ h := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show g ≠ h from (by exact dv_g_h))
  have dv_cache_0006 : g ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show g ≠ x from (by exact fresh_g_ne_x))
  have dv_cache_0007 : g ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0008 : h ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have dv_cache_0009 : h ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ y from (by exact fresh_h_ne_y))
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : f ∉ ((syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, dv_A_f, fresh_f_ne_y, dv_B_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : g ∉ ((syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_x, dv_A_g, fresh_g_ne_y, dv_B_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : h ∉ ((syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_x, dv_A_h, fresh_h_ne_y, dv_B_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((Wff.imp (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A))) (syn_wex h (syn_wf1 (.cv h) A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_A, fresh_x_ne_f, fresh_x_ne_g, fresh_x_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((Wff.imp (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A))) (syn_wex h (syn_wf1 (.cv h) A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_A, fresh_y_ne_f, fresh_y_ne_g, fresh_y_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wpp x y f g h dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_biimpi (syn_wwpp) (.all x (.all y (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x))) (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x)))) (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y)))))) p0000
  have p0002 :=
    @g_foeq3 (.cv x) A (.cv y) (.cv f)
  have p0003 :=
    @g_foeq2 (.cv y) B A (.cv f)
  have p0004 :=
    @g_sylan9bb (.classEq (.cv x) A) (syn_wfo (.cv f) (.cv y) (.cv x)) (syn_wfo (.cv f) (.cv y) A) (.classEq (.cv y) B) (syn_wfo (.cv f) B A) p0002 p0003
  have p0005 :=
    @g_exbidv (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wfo (.cv f) (.cv y) (.cv x)) (syn_wfo (.cv f) B A) f dv_cache_0011 p0004
  have p0006 :=
    @g_f1eq3 (.cv x) A (.cv y) (.cv g)
  have p0007 :=
    @g_f1eq2 (.cv y) B A (.cv g)
  have p0008 :=
    @g_sylan9bb (.classEq (.cv x) A) (syn_wf1 (.cv g) (.cv y) (.cv x)) (syn_wf1 (.cv g) (.cv y) A) (.classEq (.cv y) B) (syn_wf1 (.cv g) B A) p0006 p0007
  have p0009 :=
    @g_exbidv (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wf1 (.cv g) (.cv y) (.cv x)) (syn_wf1 (.cv g) B A) g dv_cache_0012 p0008
  have p0010 :=
    @g_anbi12d (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x))) (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x))) (syn_wex g (syn_wf1 (.cv g) B A)) p0005 p0009
  have p0011 :=
    @g_f1eq2 (.cv x) A (.cv y) (.cv h)
  have p0012 :=
    @g_f1eq3 (.cv y) B A (.cv h)
  have p0013 :=
    @g_sylan9bb (.classEq (.cv x) A) (syn_wf1 (.cv h) (.cv x) (.cv y)) (syn_wf1 (.cv h) A (.cv y)) (.classEq (.cv y) B) (syn_wf1 (.cv h) A B) p0011 p0012
  have p0014 :=
    @g_exbidv (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wf1 (.cv h) (.cv x) (.cv y)) (syn_wf1 (.cv h) A B) h dv_cache_0013 p0013
  have p0015 :=
    @g_imbi12d (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x))) (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x)))) (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A))) (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y))) (syn_wex h (syn_wf1 (.cv h) A B)) p0010 p0014
  have p0016 :=
    @g_spc2gv (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x))) (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x)))) (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y)))) (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A))) (syn_wex h (syn_wf1 (.cv h) A B))) x y A B V W dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0010 p0015
  have p0017 :=
    @g_syl5 (syn_wwpp) (.all x (.all y (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x))) (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x)))) (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y)))))) (syn_wa (.classMem A V) (.classMem B W)) (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A))) (syn_wex h (syn_wf1 (.cv h) A B))) p0001 p0016
  exact p0017

noncomputable def g_nnnzdf
    (y : Var) :
    Nominal.NPrf (.classEq (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var)
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0001 :=
    @g_peano1
  have p0002 :=
    @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c)) (syn_cnnc) p0003
  have p0005 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c)))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0000 p0004
  exact p0005

noncomputable def g_nnnzex
    (y : Var) :
    Nominal.NPrf (.classMem (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cvv)) := by
  let proofSupport : Finset Var := ({y} : Finset Var)
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0001 :=
    @g_peano1
  have p0002 :=
    @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c)) (syn_cnnc) p0003
  have p0005 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c)))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0000 p0004
  have p0006 :=
    @g_nncex
  have p0007 :=
    @g_snex (syn_c0c)
  have p0008 :=
    @g_difex (syn_cnnc) (syn_csn (syn_c0c)) p0006 p0007
  have p0009 :=
    @g_eqeltri (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) (syn_cvv) p0005 p0008
  exact p0009

noncomputable def g_fopprod
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_simpl (syn_wfo F A C) (syn_wfo G B D)
  have p0001 :=
    @g_fofn A C F
  have p0002 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo F A C) (syn_wfn F A) p0000 p0001
  have p0003 :=
    @g_simpr (syn_wfo F A C) (syn_wfo G B D)
  have p0004 :=
    @g_fofn B D G
  have p0005 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo G B D) (syn_wfn G B) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfn F A) (syn_wfn G B) p0002 p0005
  have p0007 :=
    @g_fnpprod A B F G
  have p0008 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_wfn (syn_cpprod F G) (syn_cxp A B)) p0006 p0007
  have p0009 :=
    @g_rnpprod F G
  have p0010 :=
    @g_a1i (.classEq (syn_crn (syn_cpprod F G)) (syn_cxp (syn_crn F) (syn_crn G))) (syn_wa (syn_wfo F A C) (syn_wfo G B D)) p0009
  have p0011 :=
    @g_simpl (syn_wfo F A C) (syn_wfo G B D)
  have p0012 :=
    @g_forn A C F
  have p0013 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo F A C) (.classEq (syn_crn F) C) p0011 p0012
  have p0014 :=
    @g_simpr (syn_wfo F A C) (syn_wfo G B D)
  have p0015 :=
    @g_forn B D G
  have p0016 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo G B D) (.classEq (syn_crn G) D) p0014 p0015
  have p0017 :=
    @g_xpeq12d (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_crn F) C (syn_crn G) D p0013 p0016
  have p0018 :=
    @g_eqtrd (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_crn (syn_cpprod F G)) (syn_cxp (syn_crn F) (syn_crn G)) (syn_cxp C D) p0010 p0017
  have p0019 :=
    @g_jca (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfn (syn_cpprod F G) (syn_cxp A B)) (.classEq (syn_crn (syn_cpprod F G)) (syn_cxp C D)) p0008 p0018
  have p0020 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D))))
  have p0021 :=
    @g_a1i (syn_wb (syn_wfo (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D)) (syn_wa (syn_wfn (syn_cpprod F G) (syn_cxp A B)) (.classEq (syn_crn (syn_cpprod F G)) (syn_cxp C D)))) (syn_wa (syn_wfo F A C) (syn_wfo G B D)) p0020
  have p0022 :=
    @g_mpbird (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D)) (syn_wa (syn_wfn (syn_cpprod F G) (syn_cxp A B)) (.classEq (syn_crn (syn_cpprod F G)) (syn_cxp C D))) p0019 p0021
  exact p0022

noncomputable def g_foun
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfo (syn_cun F G) (syn_cun A B) (syn_cun C D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_simpl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))
  have p0001 :=
    @g_simpl (syn_wfo F A C) (syn_wfo G B D)
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo F A C) p0000 p0001
  have p0003 :=
    @g_fofn A C F
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfo F A C) (syn_wfn F A) p0002 p0003
  have p0005 :=
    @g_simpl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))
  have p0006 :=
    @g_simpr (syn_wfo F A C) (syn_wfo G B D)
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo G B D) p0005 p0006
  have p0008 :=
    @g_fofn B D G
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfo G B D) (syn_wfn G B) p0007 p0008
  have p0010 :=
    @g_jca (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfn F A) (syn_wfn G B) p0004 p0009
  have p0011 :=
    @g_simpr (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))
  have p0012 :=
    @g_jca (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0)) p0010 p0011
  have p0013 :=
    @g_fnun A B F G
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfn (syn_cun F G) (syn_cun A B)) p0012 p0013
  have p0015 :=
    @g_rnun F G
  have p0016 :=
    @g_a1i (.classEq (syn_crn (syn_cun F G)) (syn_cun (syn_crn F) (syn_crn G))) (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) p0015
  have p0017 :=
    @g_simpl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))
  have p0018 :=
    @g_simpl (syn_wfo F A C) (syn_wfo G B D)
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo F A C) p0017 p0018
  have p0020 :=
    @g_forn A C F
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfo F A C) (.classEq (syn_crn F) C) p0019 p0020
  have p0022 :=
    @g_simpl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))
  have p0023 :=
    @g_simpr (syn_wfo F A C) (syn_wfo G B D)
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo G B D) p0022 p0023
  have p0025 :=
    @g_forn B D G
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfo G B D) (.classEq (syn_crn G) D) p0024 p0025
  have p0027 :=
    @g_uneq12d (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_crn F) C (syn_crn G) D p0021 p0026
  have p0028 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_crn (syn_cun F G)) (syn_cun (syn_crn F) (syn_crn G)) (syn_cun C D) p0016 p0027
  have p0029 :=
    @g_jca (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfn (syn_cun F G) (syn_cun A B)) (.classEq (syn_crn (syn_cun F G)) (syn_cun C D)) p0014 p0028
  have p0030 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo (syn_cun F G) (syn_cun A B) (syn_cun C D))))
  have p0031 :=
    @g_a1i (syn_wb (syn_wfo (syn_cun F G) (syn_cun A B) (syn_cun C D)) (syn_wa (syn_wfn (syn_cun F G) (syn_cun A B)) (.classEq (syn_crn (syn_cun F G)) (syn_cun C D)))) (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) p0030
  have p0032 :=
    @g_mpbird (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfo (syn_cun F G) (syn_cun A B) (syn_cun C D)) (syn_wa (syn_wfn (syn_cun F G) (syn_cun A B)) (.classEq (syn_crn (syn_cun F G)) (syn_cun C D))) p0029 p0031
  exact p0032

noncomputable def g_xnnex
    (x : Var) :
    Nominal.NPrf (.classMem (syn_cxp (.cv x) (syn_cnnc)) (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var)
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_nncex
  have p0002 :=
    @g_xpex (.cv x) (syn_cnnc) p0000 p0001
  exact p0002

noncomputable def g_padsetex
    (x : Var) (y : Var) (v : Var) (dv_v_x : v ≠ x) (dv_v_y : v ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classMem (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({v} : Finset Var)
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex v
  have p0001 :=
    @g_snex (syn_c0c)
  have p0002 :=
    @g_xpex (.cv v) (syn_csn (syn_c0c)) p0000 p0001
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0005 :=
    @g_peano1
  have p0006 :=
    @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c)) (syn_cnnc) p0007
  have p0009 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c)))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0004 p0008
  have p0010 :=
    @g_nncex
  have p0011 :=
    @g_snex (syn_c0c)
  have p0012 :=
    @g_difex (syn_cnnc) (syn_csn (syn_c0c)) p0010 p0011
  have p0013 :=
    @g_eqeltri (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) (syn_cvv) p0009 p0012
  have p0014 :=
    @g_xpex (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) p0003 p0013
  have p0015 :=
    @g_unex (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) p0002 p0014
  exact p0015

#print axioms g_padsetex

end NFChoice.DirectNominalPrf.WPPReplay
