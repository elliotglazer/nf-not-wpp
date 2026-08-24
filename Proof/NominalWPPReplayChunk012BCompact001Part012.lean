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
import NominalWPPReplayChunk012BCompact001Part011

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

noncomputable def g_dfoprab2
    (ph : Wff) (x : Var) (y : Var) (z : Var) (w : Var) (dv_ph_w : w ∉ ph.fv) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.classEq (syn_coprab x y z ph) (syn_copab w z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ({w} : Finset Var)
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_ph : v ∉ ph.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_v_ne_z : v ≠ z := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_v : z ≠ v :=
    Ne.symm fresh_v_ne_z
  have fresh_v_ne_w : v ≠ w := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w_ne_v : w ≠ v :=
    Ne.symm fresh_v_ne_w
  have dv_cache_0001 : w ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_w_x, dv_w_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_v, dv_w_x, dv_w_y, dv_w_z, dv_ph_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv v) (syn_cop (.cv w) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, (Ne.symm dv_w_x), dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv v) (syn_cop (.cv w) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, (Ne.symm dv_w_y), dv_y_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0007 : v ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0008 : v ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0009 : v ∉ ((syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_x, fresh_v_ne_y, fresh_v_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0011 : z ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show z ≠ v from (by exact fresh_z_ne_v))
  have p0000 :=
    @g_excom (syn_wex x (syn_wex y (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) z w
  have p0001 :=
    @g_exrot4 (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) z w x y
  have p0002 :=
    @g_an12 (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph
  have p0003 :=
    @g_exbii (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) ph)) w p0002
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_opex (.cv x) (.cv y) p0004 p0005
  have p0007 :=
    @g_opeq1 (.cv w) (syn_cop (.cv x) (.cv y)) (.cv z)
  have p0008 :=
    @g_eqeq2d (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_cop (.cv w) (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) (.cv v) p0007
  have p0009 :=
    @g_anbi1d (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph p0008
  have p0010 :=
    @g_ceqsexv (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) ph) (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph) w (syn_cop (.cv x) (.cv y)) dv_cache_0001 dv_cache_0002 p0006 p0009
  have p0011 :=
    @g_bitri (syn_wex w (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) ph))) (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph) p0003 p0010
  have p0012 :=
    @g_n_3exbii (syn_wex w (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph) x y z p0011
  have p0013 :=
    @g_bitri (syn_wex z (syn_wex w (syn_wex x (syn_wex y (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))) (syn_wex x (syn_wex y (syn_wex z (syn_wex w (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))) (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))) p0001 p0012
  have p0014 :=
    @g_n_19_42vv (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph) x y dv_cache_0003 dv_cache_0004
  have p0015 :=
    @g_n_2exbii (syn_wex x (syn_wex y (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) w z p0014
  have p0016 :=
    @g_n_3bitr3i (syn_wex z (syn_wex w (syn_wex x (syn_wex y (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))) (syn_wex w (syn_wex z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))) (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))) (syn_wex w (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))) p0000 p0013 p0015
  have p0017 :=
    @g_abbii (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))) (syn_wex w (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))) v p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oprab ph x y z v dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0019 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) w z v dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0020 :=
    @g_n_3eqtr4i (.cab v (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))) (.cab v (syn_wex w (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))))) (syn_coprab x y z ph) (syn_copab w z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) p0017 p0018 p0019
  exact p0020

noncomputable def g_oprabbid
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_oprabbid_1 : Nominal.NPrf (syn_wnf x ph)) (hyp_oprabbid_2 : Nominal.NPrf (syn_wnf y ph)) (hyp_oprabbid_3 : Nominal.NPrf (syn_wnf z ph)) (hyp_oprabbid_4 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_coprab x y z ps) (syn_coprab x y z ch))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_ch : w ∉ ch.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have dv_cache_0001 : w ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (ps).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ps, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : w ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0004 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0005 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0006 : w ∉ (ch).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ch, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_anbi2d ph ps ch (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) hyp_oprabbid_4
  have p0001 :=
    @g_exbid ph (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps) (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch) z hyp_oprabbid_3 p0000
  have p0002 :=
    @g_exbid ph (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps)) (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch)) y hyp_oprabbid_2 p0001
  have p0003 :=
    @g_exbid ph (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch))) x hyp_oprabbid_1 p0002
  have p0004 :=
    @g_abbidv ph (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps)))) (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch)))) w dv_cache_0001 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oprab ps x y z w dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oprab ch x y z w dv_cache_0006 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0007 :=
    @g_n_3eqtr4g ph (.cab w (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps))))) (.cab w (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch))))) (syn_coprab x y z ps) (syn_coprab x y z ch) p0004 p0005 p0006
  exact p0007

noncomputable def g_oprabbidv
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (z : Var) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_oprabbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_coprab x y z ps) (syn_coprab x y z ch))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (ph).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0005 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_nfv ph x dv_cache_0001
  have p0001 :=
    @g_nfv ph y dv_cache_0002
  have p0002 :=
    @g_nfv ph z dv_cache_0003
  have p0003 :=
    @g_oprabbid ph ps ch x y z dv_cache_0004 dv_cache_0005 p0000 p0001 p0002 hyp_oprabbidv_1
  exact p0003

noncomputable def g_oprabbii
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_oprabbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (.classEq (syn_coprab x y z ph) (syn_coprab x y z ps)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv w) (.cv w))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv w) (.cv w))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Wff.classEq (.cv w) (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0005 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_eqid (.cv w)
  have p0001 :=
    @g_a1i (syn_wb ph ps) (.classEq (.cv w) (.cv w)) hyp_oprabbii_1
  have p0002 :=
    @g_oprabbidv (.classEq (.cv w) (.cv w)) ph ps x y z dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0001
  have p0003 :=
    Nominal.mp p0000 p0002
  exact p0003

noncomputable def g_cbvoprab12
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (w : Var) (v : Var) (dv_v_w : v ≠ w) (dv_v_x : v ≠ x) (dv_v_y : v ≠ y) (dv_v_z : v ≠ z) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_cbvoprab12_1 : Nominal.NPrf (syn_wnf w ph)) (hyp_cbvoprab12_2 : Nominal.NPrf (syn_wnf v ph)) (hyp_cbvoprab12_3 : Nominal.NPrf (syn_wnf x ps)) (hyp_cbvoprab12_4 : Nominal.NPrf (syn_wnf y ps)) (hyp_cbvoprab12_5 : Nominal.NPrf (.imp (syn_wa (.objEq x w) (.objEq y v)) (syn_wb ph ps))) :
    Nominal.NPrf (.classEq (syn_coprab x y z ph) (syn_coprab w v z ps)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ({w} : Finset Var) ∪ ({v} : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_ph : u ∉ ph.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_u_not_ps : u ∉ ps.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_u : z ≠ u :=
    Ne.symm fresh_u_ne_z
  have fresh_u_ne_w : u ≠ w := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_u : w ≠ u :=
    Ne.symm fresh_u_ne_w
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have dv_cache_0001 : w ∉ ((Wff.classEq (.cv u) (syn_cop (.cv x) (.cv y)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_u, dv_w_x, dv_w_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((Wff.classEq (.cv u) (syn_cop (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, dv_v_x, dv_v_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv u) (syn_cop (.cv w) (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, (Ne.symm dv_w_x), (Ne.symm dv_v_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv u) (syn_cop (.cv w) (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, (Ne.symm dv_w_y), (Ne.symm dv_v_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ x from (by exact dv_v_x))
  have dv_cache_0006 : v ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ w from (by exact dv_v_w))
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : y ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show y ≠ w from (by exact Ne.symm dv_w_y))
  have dv_cache_0009 : u ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0011 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0012 : u ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0013 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0014 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0015 : u ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_ps, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : u ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0017 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0018 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show w ≠ z from (by exact dv_w_z))
  have dv_cache_0019 : v ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show v ≠ z from (by exact dv_v_z))
  have p0000 :=
    @g_nfv (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) w dv_cache_0001
  have p0001 :=
    @g_nfan (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph w p0000 hyp_cbvoprab12_1
  have p0002 :=
    @g_nfv (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) v dv_cache_0002
  have p0003 :=
    @g_nfan (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph v p0002 hyp_cbvoprab12_2
  have p0004 :=
    @g_nfv (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) x dv_cache_0003
  have p0005 :=
    @g_nfan (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps x p0004 hyp_cbvoprab12_3
  have p0006 :=
    @g_nfv (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) y dv_cache_0004
  have p0007 :=
    @g_nfan (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps y p0006 hyp_cbvoprab12_4
  have p0008 :=
    @g_opeq12 (.cv x) (.cv w) (.cv y) (.cv v)
  have p0009_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objEq x w) (.objEq y v)) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop (.cv w) (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0008
  have p0009 :=
    @g_eqeq2d (syn_wa (.objEq x w) (.objEq y v)) (syn_cop (.cv x) (.cv y)) (syn_cop (.cv w) (.cv v)) (.cv u) p0009_e00_recanon
  have p0010 :=
    @g_anbi12d (syn_wa (.objEq x w) (.objEq y v)) (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ph ps p0009 hyp_cbvoprab12_5
  have p0011 :=
    @g_cbvex2 (syn_wa (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph) (syn_wa (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps) x y w v dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0001 p0003 p0005 p0007 p0010
  have p0012 :=
    @g_opabbii (syn_wex x (syn_wex y (syn_wa (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph))) (syn_wex w (syn_wex v (syn_wa (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps))) u z p0011
  have p0013 :=
    @g_dfoprab2 ph x y z u dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0014 :=
    @g_dfoprab2 ps w v z u dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0012 dv_cache_0018 dv_cache_0019
  have p0015 :=
    @g_n_3eqtr4i (syn_copab u z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph)))) (syn_copab u z (syn_wex w (syn_wex v (syn_wa (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps)))) (syn_coprab x y z ph) (syn_coprab w v z ps) p0012 p0013 p0014
  exact p0015

noncomputable def g_dmoprab
    (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.classEq (syn_cdm (syn_coprab x y z ph)) (syn_copab x y (syn_wex z ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have dv_cache_0001 : w ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ≠ x := by
    clear dv_cache_0001
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0003 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0004 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0007 : z ∉ ((Wff.classEq (.cv w) (syn_cop (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, (Ne.symm dv_x_z), (Ne.symm dv_y_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((syn_wex z ph)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0010 : y ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have p0000 :=
    @g_dfoprab2 ph x y z w dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_dmeqi (syn_coprab x y z ph) (syn_copab w z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) p0000
  have p0002 :=
    @g_dmopab (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) w z dv_cache_0004
  have p0003 :=
    @g_exrot3 (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph) z x y
  have p0004 :=
    @g_n_19_42v (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph z dv_cache_0007
  have p0005 :=
    @g_n_2exbii (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wex z ph)) x y p0004
  have p0006 :=
    @g_bitri (syn_wex z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wex z ph)))) p0003 p0005
  have p0007 :=
    @g_abbii (syn_wex z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wex z ph)))) w p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab (syn_wex z ph) x y w dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0009 :=
    @g_eqtr4i (.cab w (syn_wex z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))) (.cab w (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wex z ph))))) (syn_copab x y (syn_wex z ph)) p0007 p0008
  have p0010 :=
    @g_n_3eqtri (syn_cdm (syn_coprab x y z ph)) (syn_cdm (syn_copab w z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))) (.cab w (syn_wex z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))) (syn_copab x y (syn_wex z ph)) p0001 p0002 p0009
  exact p0010

#print axioms g_dmoprab

end NFChoice.DirectNominalPrf.WPPReplay
