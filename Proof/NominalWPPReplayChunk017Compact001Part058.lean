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
import NominalWPPReplayChunk017Compact001Part057

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

noncomputable def g_wppgammatchwboundedeqndv
    (x : Var) (C : Class) (F : Class) (G : Class) (r : Var) (p : Var) (dv_C_p : p ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_G_p : p ∉ G.fv) (dv_G_r : r ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_p_r : p ≠ r) (dv_p_x : p ≠ x) (dv_r_x : r ≠ x) (hyp_wppgammatchwboundedeqndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppgammatchwboundedeqndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppgammatchwboundedeqndv_3 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppgammatchwboundedeqndv_4 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppgammatchwboundedeqndv_5 : Nominal.NPrf (syn_wral x (syn_cdm F) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x)))))) (hyp_wppgammatchwboundedeqndv_6 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G)))))) (hyp_wppgammatchwboundedeqndv_7 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs)))))) (hyp_wppgammatchwboundedeqndv_8 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_cwppgamma G (syn_ctc C))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ F.fv ∪ G.fv ∪ ({r} : Finset Var) ∪ ({p} : Finset Var)
  let k : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_ne_x : k ≠ x := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_k : x ≠ k :=
    Ne.symm fresh_k_ne_x
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_k_not_G : k ∉ G.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_ne_r : k ≠ r := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_r_ne_k : r ≠ k :=
    Ne.symm fresh_k_ne_r
  have fresh_k_ne_p : k ≠ p := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_k : p ≠ k :=
    Ne.symm fresh_k_ne_p
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_ne_x : d ≠ x := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_G : d ∉ G.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_ne_r : d ≠ r := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_r_ne_d : r ≠ d :=
    Ne.symm fresh_d_ne_r
  have fresh_d_ne_p : d ≠ p := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_d : p ≠ d :=
    Ne.symm fresh_d_ne_p
  have fresh_k_ne_d : k ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_k : d ≠ k :=
    Ne.symm fresh_k_ne_d
  have dv_cache_0001 : d ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : r ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : d ≠ k := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show d ≠ k from (by exact fresh_d_ne_k))
  have dv_cache_0014 : d ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show d ≠ p from (by exact fresh_d_ne_p))
  have dv_cache_0015 : d ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have dv_cache_0016 : d ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0017 : k ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show k ≠ p from (by exact fresh_k_ne_p))
  have dv_cache_0018 : k ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show k ≠ r from (by exact fresh_k_ne_r))
  have dv_cache_0019 : k ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show k ≠ x from (by exact fresh_k_ne_x))
  have dv_cache_0020 : p ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show p ≠ r from (by exact dv_p_r))
  have dv_cache_0021 : p ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show p ≠ x from (by exact dv_p_x))
  have dv_cache_0022 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show r ≠ x from (by exact dv_r_x))
  have dv_cache_0023 : k ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : k ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : k ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex F (syn_cfuns)
  have p0001 :=
    Nominal.mp hyp_wppgammatchwboundedeqndv_1 p0000
  have p0002 :=
    @g_elex G (syn_cfuns)
  have p0003 :=
    Nominal.mp hyp_wppgammatchwboundedeqndv_3 p0002
  have p0004 :=
    @g_hwcardstcclndv C
  have p0005 :=
    Nominal.mp hyp_wppgammatchwboundedeqndv_8 p0004
  have p0006 :=
    @g_wppcandtchwboundedimagebindv x C k F G r p d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 hyp_wppgammatchwboundedeqndv_1 hyp_wppgammatchwboundedeqndv_2 hyp_wppgammatchwboundedeqndv_3 hyp_wppgammatchwboundedeqndv_4 hyp_wppgammatchwboundedeqndv_5 hyp_wppgammatchwboundedeqndv_6 hyp_wppgammatchwboundedeqndv_7 hyp_wppgammatchwboundedeqndv_8
  have p0007 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d))))))
  have p0008 :=
    @g_bitr4i (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))) (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d)))) p0006 p0007
  have p0009 :=
    Nominal.gen p0008 k
  have p0010 :=
    @g_wppgammaimagetceqndv C k F G d dv_cache_0001 dv_cache_0023 dv_cache_0005 dv_cache_0024 dv_cache_0009 dv_cache_0025 dv_cache_0013 p0001 hyp_wppgammatchwboundedeqndv_8 p0003 p0005 p0009
  exact p0010

noncomputable def g_wppgammadomhwndv
    (C : Class) (F : Class) (p : Var) (dv_C_p : p ∉ C.fv) (dv_F_p : p ∉ F.fv) (hyp_wppgammadomhwndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wppgammadomhwndv_2 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) (hyp_wppgammadomhwndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classMem (syn_cwppgamma F C) (syn_cdm F)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ ({p} : Finset Var)
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_ne_p : k ≠ p := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_k : p ≠ k :=
    Ne.symm fresh_k_ne_p
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
  have dv_cache_0003 : p ∉ ((syn_cwppgamma F C)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((Wff.imp (syn_wbr (syn_cwppgamma F C) (syn_clec) C) (.classMem (syn_cwppgamma F C) (syn_cdm F)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) hyp_wppgammadomhwndv_1 hyp_wppgammadomhwndv_3
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
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)) (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_simpr (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) hyp_wppgammadomhwndv_1 hyp_wppgammadomhwndv_3
  have p0013 :=
    @g_wppgammaminhwndv C k F dv_cache_0001 dv_cache_0002
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_elwppcand C (syn_cwppgamma F C) F
  have p0018 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)) (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))) p0017
  have p0019 :=
    Nominal.mp p0016 p0018
  have p0020 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)) (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F C) (syn_clec) C)
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_pm3_2i (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))) p0023 hyp_wppgammadomhwndv_2
  have p0025 :=
    @g_id (.classEq (.cv p) (syn_cwppgamma F C))
  have p0026 :=
    @g_breq1d (.classEq (.cv p) (syn_cwppgamma F C)) (.cv p) (syn_cwppgamma F C) C (syn_clec) p0025
  have p0027 :=
    @g_id (.classEq (.cv p) (syn_cwppgamma F C))
  have p0028 :=
    @g_eleq1d (.classEq (.cv p) (syn_cwppgamma F C)) (.cv p) (syn_cwppgamma F C) (syn_cdm F) p0027
  have p0029 :=
    @g_imbi12d (.classEq (.cv p) (syn_cwppgamma F C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cwppgamma F C) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_cwppgamma F C) (syn_cdm F)) p0026 p0028
  have p0030 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))) (.imp (syn_wbr (syn_cwppgamma F C) (syn_clec) C) (.classMem (syn_cwppgamma F C) (syn_cdm F))) p (syn_cwppgamma F C) (syn_chwcards (syn_cvv)) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0029
  have p0031 :=
    Nominal.mp p0024 p0030
  have p0032 :=
    Nominal.mp p0011 p0031
  exact p0032

noncomputable def g_wppgammareachexhwndv
    (C : Class) (n : Var) (F : Class) (p : Var) (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_n_p : n ≠ p) (hyp_wppgammareachexhwndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppgammareachexhwndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppgammareachexhwndv_3 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) (hyp_wppgammareachexhwndv_4 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv n)))) := by
  let proofSupport : Finset Var := C.fv ∪ ({n} : Finset Var) ∪ F.fv ∪ ({p} : Finset Var)
  have dv_cache_0001 : p ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((syn_cwppgamma F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex F (syn_cfuns)
  have p0001 :=
    Nominal.mp hyp_wppgammareachexhwndv_1 p0000
  have p0002 :=
    @g_wppgammareachndv C F p0001 hyp_wppgammareachexhwndv_4
  have p0003 :=
    @g_elex F (syn_cfuns)
  have p0004 :=
    Nominal.mp hyp_wppgammareachexhwndv_1 p0003
  have p0005 :=
    @g_wppgammadomhwndv C F p dv_cache_0001 dv_cache_0002 p0004 hyp_wppgammareachexhwndv_3 hyp_wppgammareachexhwndv_4
  have p0006 :=
    @g_elex C (syn_chwcards (syn_cvv))
  have p0007 :=
    Nominal.mp hyp_wppgammareachexhwndv_4 p0006
  have p0008 :=
    @g_wppreachfwdrexvndv C (syn_cwppgamma F C) n F dv_cache_0003 dv_cache_0004 dv_cache_0005 hyp_wppgammareachexhwndv_1 p0005 hyp_wppgammareachexhwndv_2 p0007
  have p0009 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_cwppreach F C)) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv n)))) p0008
  have p0010 :=
    Nominal.mp p0002 p0009
  exact p0010

noncomputable def g_wppgammaleasthithwndv
    (C : Class) (m : Var) (n : Var) (F : Class) (p : Var) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_m_n : m ≠ n) (hyp_wppgammaleasthithwndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppgammaleasthithwndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppgammaleasthithwndv_3 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) (hyp_wppgammaleasthithwndv_4 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m) (syn_cwpphit F (syn_cwppgamma F C) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F (syn_cwppgamma F C) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) := by
  let proofSupport : Finset Var := C.fv ∪ ({m} : Finset Var) ∪ ({n} : Finset Var) ∪ F.fv ∪ ({p} : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_q_ne_m : q ≠ m := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_m_ne_q : m ≠ q :=
    Ne.symm fresh_q_ne_m
  have fresh_q_ne_n : q ≠ n := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_q : n ≠ q :=
    Ne.symm fresh_q_ne_n
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have dv_cache_0001 : q ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ p from (by exact fresh_q_ne_p))
  have dv_cache_0006 : m ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((syn_cwppgamma F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((syn_cwppgamma F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((syn_cwppgamma F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, fresh_q_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : m ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : q ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0017 : m ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show m ≠ q from (by exact fresh_m_ne_q))
  have dv_cache_0018 : n ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show n ≠ q from (by exact fresh_n_ne_q))
  have p0000 :=
    @g_finlewe
  have p0001 :=
    @g_wppgammareachexhwndv C q F p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 hyp_wppgammaleasthithwndv_1 hyp_wppgammaleasthithwndv_2 hyp_wppgammaleasthithwndv_3 hyp_wppgammaleasthithwndv_4
  have p0002 :=
    @g_elex F (syn_cfuns)
  have p0003 :=
    Nominal.mp hyp_wppgammaleasthithwndv_1 p0002
  have p0004 :=
    @g_wppgammadomhwndv C F p dv_cache_0002 dv_cache_0004 p0003 hyp_wppgammaleasthithwndv_3 hyp_wppgammaleasthithwndv_4
  have p0005 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem (syn_cwppgamma F C) (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wppgammaleasthithwndv_1 p0004 hyp_wppgammaleasthithwndv_2
  have p0006 :=
    @g_elwpphitvndv C F (syn_cwppgamma F C) (.cv q)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_biimpri (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv q)))) p0007
  have p0009 :=
    @g_expcom (.classMem (.cv q) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv q))) (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C)) p0008
  have p0010 :=
    @g_com12 (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv q))) (.classMem (.cv q) (syn_cnnc)) (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C)) p0009
  have p0011 :=
    @g_reximia (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv q))) (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C)) q (syn_cnnc) p0010
  have p0012 :=
    Nominal.mp p0001 p0011
  have p0013 :=
    @g_pm3_2i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wrex q (syn_cnnc) (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C))) p0000 p0012
  have p0014 :=
    @g_elex F (syn_cfuns)
  have p0015 :=
    Nominal.mp hyp_wppgammaleasthithwndv_1 p0014
  have p0016 :=
    @g_wpphitminexvndv q C (syn_ckqrel (syn_clefin)) m n F (syn_cwppgamma F C) dv_cache_0006 dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0003 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0015
  have p0017 :=
    Nominal.mp p0013 p0016
  exact p0017

#print axioms g_wppgammaleasthithwndv

end NFChoice.DirectNominalPrf.WPPReplay
