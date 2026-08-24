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
import NominalWPPReplayChunk013Compact001Part027

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

noncomputable def g_weds
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_weds_1 : Nominal.NPrf (.classMem (.cab x ps) (syn_cvv))) (hyp_weds_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ps ch))) (hyp_weds_3 : Nominal.NPrf (.imp (.objEq x z) (syn_wb ps th))) (hyp_weds_4 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cwe) A))) (hyp_weds_5 : Nominal.NPrf (.imp ph (syn_wrex x A ps))) :
    Nominal.NPrf (.imp ph (syn_wrex y A (syn_wa ch (syn_wral z A (.imp th (syn_wbr (.cv y) R (.cv z))))))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ R.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (ch).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ch_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (th).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_th_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0011 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0012 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0013 : z ∉ ((syn_wa ph (.classMem (.cv y) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, (Ne.symm dv_y_z), dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0001 :=
    @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 :=
    @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A) (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simprbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A) p0003
  have p0005 :=
    @g_syl ph (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cfound) A) hyp_weds_4 p0004
  have p0006 :=
    @g_frds ph ps ch th x y z A R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_weds_1 hyp_weds_2 hyp_weds_3 p0005 hyp_weds_5
  have p0007 :=
    @g_impexp th (syn_wbr (.cv z) R (.cv y)) (.objEq z y)
  have p0008 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A) p0003
  have p0009 :=
    @g_syl ph (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) hyp_weds_4 p0008
  have p0010 :=
    @g_sopc A R
  have p0011 :=
    @g_simprbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A) p0010
  have p0012 :=
    @g_syl ph (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cconnex) A) p0009 p0011
  have p0013 :=
    @g_adantr ph (syn_wbr R (syn_cconnex) A) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A)) p0012
  have p0014 :=
    @g_simprl ph (.classMem (.cv y) A) (.classMem (.cv z) A)
  have p0015 :=
    @g_simprr ph (.classMem (.cv y) A) (.classMem (.cv z) A)
  have p0016 :=
    @g_connexd (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) A R (.cv y) (.cv z) p0013 p0014 p0015
  have p0017 :=
    @g_ax1 (syn_wbr (.cv y) R (.cv z)) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))
  have p0018 :=
    @g_a1i (.imp (syn_wbr (.cv y) R (.cv z)) (.imp (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) p0017
  have p0019 :=
    @g_pm2_27 (syn_wbr (.cv z) R (.cv y)) (.objEq z y)
  have p0020 :=
    @g_porta A R
  have p0021 :=
    @g_simp1bi (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A) p0020
  have p0022 :=
    @g_adantr (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A) (syn_wbr R (syn_cconnex) A) p0021
  have p0023 :=
    @g_sylbi (syn_wbr R (syn_cstrict) A) (syn_wa (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A)) (syn_wbr R (syn_cref) A) p0010 p0022
  have p0024 :=
    @g_syl ph (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cref) A) p0009 p0023
  have p0025 :=
    @g_adantr ph (syn_wbr R (syn_cref) A) (.classMem (.cv z) A) p0024
  have p0026 :=
    @g_simpr ph (.classMem (.cv z) A)
  have p0027 :=
    @g_refd (syn_wa ph (.classMem (.cv z) A)) A R (.cv z) p0025 p0026
  have p0028 :=
    @g_adantrl ph (.classMem (.cv z) A) (syn_wbr (.cv z) R (.cv z)) (.classMem (.cv y) A) p0027
  have p0029 :=
    @g_breq1 (.cv z) (.cv y) (.cv z) R
  have p0030_e01_recanon : Nominal.NPrf (.imp (.objEq z y) (syn_wb (syn_wbr (.cv z) R (.cv z)) (syn_wbr (.cv y) R (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0029
  have p0030 :=
    @g_syl5ibcom (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) (syn_wbr (.cv z) R (.cv z)) (.objEq z y) (syn_wbr (.cv y) R (.cv z)) p0028 p0030_e01_recanon
  have p0031 :=
    @g_syl9r (syn_wbr (.cv z) R (.cv y)) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) (.objEq z y) (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) (syn_wbr (.cv y) R (.cv z)) p0019 p0030
  have p0032 :=
    @g_jaod (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) (syn_wbr (.cv y) R (.cv z)) (.imp (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) (syn_wbr (.cv y) R (.cv z))) (syn_wbr (.cv z) R (.cv y)) p0018 p0031
  have p0033 :=
    @g_mpd (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) (syn_wo (syn_wbr (.cv y) R (.cv z)) (syn_wbr (.cv z) R (.cv y))) (.imp (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) (syn_wbr (.cv y) R (.cv z))) p0016 p0032
  have p0034 :=
    @g_imim2d (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) (syn_wbr (.cv y) R (.cv z)) th p0033
  have p0035 :=
    @g_syl5bi (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)) (.imp th (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))) (syn_wa ph (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) A))) (.imp th (syn_wbr (.cv y) R (.cv z))) p0007 p0034
  have p0036 :=
    @g_anassrs ph (.classMem (.cv y) A) (.classMem (.cv z) A) (.imp (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)) (.imp th (syn_wbr (.cv y) R (.cv z)))) p0035
  have p0037 :=
    @g_ralimdva (syn_wa ph (.classMem (.cv y) A)) (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)) (.imp th (syn_wbr (.cv y) R (.cv z))) z A dv_cache_0013 p0036
  have p0038 :=
    @g_anim2d (syn_wa ph (.classMem (.cv y) A)) (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))) (syn_wral z A (.imp th (syn_wbr (.cv y) R (.cv z)))) ch p0037
  have p0039 :=
    @g_reximdva ph (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))) (syn_wa ch (syn_wral z A (.imp th (syn_wbr (.cv y) R (.cv z))))) y A dv_cache_0014 p0038
  have p0040 :=
    @g_mpd ph (syn_wrex y A (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))) (syn_wrex y A (syn_wa ch (syn_wral z A (.imp th (syn_wbr (.cv y) R (.cv z)))))) p0006 p0039
  exact p0040

noncomputable def g_iserd
    (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_iserd_1 : Nominal.NPrf (.imp ph (.classMem R V))) (hyp_iserd_2 : Nominal.NPrf (.imp ph (.classMem A W))) (hyp_iserd_3 : Nominal.NPrf (.imp (syn_w3a ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (.cv y) R (.cv x)))) (hyp_iserd_4 : Nominal.NPrf (.imp (syn_w3a ph (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wbr (.cv x) R (.cv z)))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ R.fv ∪ V.fv ∪ W.fv
  let r : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_ph : r ∉ ph.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_r_ne_z : r ≠ z := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_r : z ≠ r :=
    Ne.symm fresh_r_ne_z
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_V : r ∉ V.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_W : r ∉ W.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_ph : a ∉ ph.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_V : a ∉ V.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_W : a ∉ W.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_r_ne_a : r ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    Ne.symm fresh_r_ne_a
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (ph).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv r) R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv r) R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0011 : a ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0012 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0013 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0014 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0015 : r ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : r ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : r ∉ ((syn_wral x A (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((syn_wral x A (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0022 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0028 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_n_3expia ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)) hyp_iserd_3
  have p0001 :=
    @g_ralrimivva ph (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) x y A A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000
  have p0002 :=
    @g_breq (.cv x) (.cv y) (.cv r) R
  have p0003 :=
    @g_breq (.cv y) (.cv x) (.cv r) R
  have p0004 :=
    @g_imbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)) (syn_wbr (.cv y) R (.cv x)) p0002 p0003
  have p0005 :=
    @g_n_2ralbidv (.classEq (.cv r) R) (.imp (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) x y (.cv a) (.cv a) dv_cache_0005 dv_cache_0006 p0004
  have p0006 :=
    @g_raleq (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) y (.cv a) A dv_cache_0007 dv_cache_0001
  have p0007 :=
    @g_raleqbi1dv (syn_wral y (.cv a) (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) x (.cv a) A dv_cache_0008 dv_cache_0009 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sym x y r a dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0009 :=
    @g_brabg (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) (syn_wral x A (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) r a R A V W (syn_csym) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0005 p0007 p0008
  have p0010 :=
    @g_syl2anc ph (.classMem R V) (.classMem A W) (syn_wb (syn_wbr R (syn_csym) A) (syn_wral x A (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))) hyp_iserd_1 hyp_iserd_2 p0009
  have p0011 :=
    @g_mpbird ph (syn_wbr R (syn_csym) A) (syn_wral x A (syn_wral y A (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) p0001 p0010
  have p0012 :=
    @g_trrd ph x y z A R V W dv_cache_0009 dv_cache_0001 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0002 dv_cache_0003 dv_cache_0026 dv_cache_0004 dv_cache_0027 dv_cache_0028 hyp_iserd_1 hyp_iserd_2 hyp_iserd_4
  have p0013 :=
    @g_ersymtr A R
  have p0014 :=
    @g_sylanbrc ph (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cer) A) p0011 p0012 p0013
  exact p0014

noncomputable def g_dfec2
    (y : Var) (A : Class) (R : Class) (dv_A_y : y ∉ A.fv) (dv_R_y : y ∉ R.fv) :
    Nominal.NPrf (.classEq (syn_cec A R) (.cab y (syn_wbr A R (.cv y)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ R.fv
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec A R)))
  have p0001 :=
    @g_imasn y A R dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_eqtri (syn_cec A R) (syn_cima R (syn_csn A)) (.cab y (syn_wbr A R (.cv y))) p0000 p0001
  exact p0002

noncomputable def g_ecexg
    (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (.classMem R B) (.classMem (syn_cec A R) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec A R)))
  have p0001 :=
    @g_snex A
  have p0002 :=
    @g_imaexg R (syn_csn A) B (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem R B) (.classMem (syn_csn A) (syn_cvv)) (.classMem (syn_cima R (syn_csn A)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem R B) (syn_cec A R) (syn_cima R (syn_csn A)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_ecexr
    (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cec B R)) (.classMem B (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    @g_n0i (syn_cima R (syn_csn B)) A
  have p0001 :=
    @g_snprc B
  have p0002 :=
    @g_imaeq2 (syn_csn B) (syn_c0) R
  have p0003 :=
    @g_sylbi (.neg (.classMem B (syn_cvv))) (.classEq (syn_csn B) (syn_c0)) (.classEq (syn_cima R (syn_csn B)) (syn_cima R (syn_c0))) p0001 p0002
  have p0004 :=
    @g_ima0 R
  have p0005 :=
    @g_syl6eq (.neg (.classMem B (syn_cvv))) (syn_cima R (syn_csn B)) (syn_cima R (syn_c0)) (syn_c0) p0003 p0004
  have p0006 :=
    @g_nsyl2 (.classMem A (syn_cima R (syn_csn B))) (.classEq (syn_cima R (syn_csn B)) (syn_c0)) (.classMem B (syn_cvv)) p0000 p0005
  have p0007 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec B R)))
  have p0008 :=
    @g_eleq2s (.classMem B (syn_cvv)) A (syn_cima R (syn_csn B)) (syn_cec B R) p0006 p0007
  exact p0008

noncomputable def g_ersym
    (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class) (hyp_ersym_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A))) (hyp_ersym_2 : Nominal.NPrf (.imp ph (.classMem X A))) (hyp_ersym_3 : Nominal.NPrf (.imp ph (.classMem Y A))) (hyp_ersym_4 : Nominal.NPrf (.imp ph (syn_wbr X R Y))) :
    Nominal.NPrf (.imp ph (syn_wbr Y R X)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  have p0000 :=
    @g_ersymtr A R
  have p0001 :=
    @g_simplbi (syn_wbr R (syn_cer) A) (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A) p0000
  have p0002 :=
    @g_syl ph (syn_wbr R (syn_cer) A) (syn_wbr R (syn_csym) A) hyp_ersym_1 p0001
  have p0003 :=
    @g_symd ph A R X Y p0002 hyp_ersym_2 hyp_ersym_3 hyp_ersym_4
  exact p0003

noncomputable def g_ersymb
    (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class) (hyp_ersymb_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A))) (hyp_ersymb_2 : Nominal.NPrf (.imp ph (.classMem X A))) (hyp_ersymb_3 : Nominal.NPrf (.imp ph (.classMem Y A))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wbr X R Y) (syn_wbr Y R X))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  have p0000 :=
    @g_adantr ph (syn_wbr R (syn_cer) A) (syn_wbr X R Y) hyp_ersymb_1
  have p0001 :=
    @g_adantr ph (.classMem X A) (syn_wbr X R Y) hyp_ersymb_2
  have p0002 :=
    @g_adantr ph (.classMem Y A) (syn_wbr X R Y) hyp_ersymb_3
  have p0003 :=
    @g_simpr ph (syn_wbr X R Y)
  have p0004 :=
    @g_ersym (syn_wa ph (syn_wbr X R Y)) A R X Y p0000 p0001 p0002 p0003
  have p0005 :=
    @g_adantr ph (syn_wbr R (syn_cer) A) (syn_wbr Y R X) hyp_ersymb_1
  have p0006 :=
    @g_adantr ph (.classMem Y A) (syn_wbr Y R X) hyp_ersymb_3
  have p0007 :=
    @g_adantr ph (.classMem X A) (syn_wbr Y R X) hyp_ersymb_2
  have p0008 :=
    @g_simpr ph (syn_wbr Y R X)
  have p0009 :=
    @g_ersym (syn_wa ph (syn_wbr Y R X)) A R Y X p0005 p0006 p0007 p0008
  have p0010 :=
    @g_impbida ph (syn_wbr X R Y) (syn_wbr Y R X) p0004 p0009
  exact p0010

noncomputable def g_ertr
    (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class) (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A))) (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A))) (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A))) (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) (syn_wbr X R Z))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv ∪ Z.fv
  have p0000 :=
    @g_ersymtr A R
  have p0001 :=
    @g_simprbi (syn_wbr R (syn_cer) A) (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A) p0000
  have p0002 :=
    @g_syl ph (syn_wbr R (syn_cer) A) (syn_wbr R (syn_ctrans) A) hyp_ertr_1 p0001
  have p0003 :=
    @g_adantr ph (syn_wbr R (syn_ctrans) A) (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) p0002
  have p0004 :=
    @g_adantr ph (.classMem X A) (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) hyp_ertr_2
  have p0005 :=
    @g_adantr ph (.classMem Y A) (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) hyp_ertr_3
  have p0006 :=
    @g_adantr ph (.classMem Z A) (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) hyp_ertr_4
  have p0007 :=
    @g_simprl ph (syn_wbr X R Y) (syn_wbr Y R Z)
  have p0008 :=
    @g_simprr ph (syn_wbr X R Y) (syn_wbr Y R Z)
  have p0009 :=
    @g_trd (syn_wa ph (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z))) A R X Y Z p0003 p0004 p0005 p0006 p0007 p0008
  have p0010 :=
    @g_ex ph (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) (syn_wbr X R Z) p0009
  exact p0010

noncomputable def g_ertrd
    (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class) (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A))) (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A))) (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A))) (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A))) (hyp_ertrd_5 : Nominal.NPrf (.imp ph (syn_wbr X R Y))) (hyp_ertrd_6 : Nominal.NPrf (.imp ph (syn_wbr Y R Z))) :
    Nominal.NPrf (.imp ph (syn_wbr X R Z)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv ∪ Z.fv
  have p0000 :=
    @g_ersymtr A R
  have p0001 :=
    @g_simprbi (syn_wbr R (syn_cer) A) (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A) p0000
  have p0002 :=
    @g_syl ph (syn_wbr R (syn_cer) A) (syn_wbr R (syn_ctrans) A) hyp_ertr_1 p0001
  have p0003 :=
    @g_trd ph A R X Y Z p0002 hyp_ertr_2 hyp_ertr_3 hyp_ertr_4 hyp_ertrd_5 hyp_ertrd_6
  exact p0003

noncomputable def g_ertr3d
    (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class) (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A))) (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A))) (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A))) (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A))) (hyp_ertr3d_5 : Nominal.NPrf (.imp ph (syn_wbr Y R X))) (hyp_ertr3d_6 : Nominal.NPrf (.imp ph (syn_wbr Y R Z))) :
    Nominal.NPrf (.imp ph (syn_wbr X R Z)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv ∪ Z.fv
  have p0000 :=
    @g_ersym ph A R Y X hyp_ertr_1 hyp_ertr_3 hyp_ertr_2 hyp_ertr3d_5
  have p0001 :=
    @g_ertrd ph A R X Y Z hyp_ertr_1 hyp_ertr_2 hyp_ertr_3 hyp_ertr_4 p0000 hyp_ertr3d_6
  exact p0001

noncomputable def g_ertr4d
    (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class) (Z : Class) (hyp_ertr_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) A))) (hyp_ertr_2 : Nominal.NPrf (.imp ph (.classMem X A))) (hyp_ertr_3 : Nominal.NPrf (.imp ph (.classMem Y A))) (hyp_ertr_4 : Nominal.NPrf (.imp ph (.classMem Z A))) (hyp_ertr4d_5 : Nominal.NPrf (.imp ph (syn_wbr X R Y))) (hyp_ertr4d_6 : Nominal.NPrf (.imp ph (syn_wbr Z R Y))) :
    Nominal.NPrf (.imp ph (syn_wbr X R Z)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv ∪ Z.fv
  have p0000 :=
    @g_ersym ph A R Z Y hyp_ertr_1 hyp_ertr_4 hyp_ertr_3 hyp_ertr4d_6
  have p0001 :=
    @g_ertrd ph A R X Y Z hyp_ertr_1 hyp_ertr_2 hyp_ertr_3 hyp_ertr_4 hyp_ertr4d_5 p0000
  exact p0001

noncomputable def g_erref
    (ph : Wff) (A : Class) (R : Class) (X : Class) (hyp_erref_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv)))) (hyp_erref_2 : Nominal.NPrf (.imp ph (.classEq (syn_cdm R) A))) (hyp_erref_3 : Nominal.NPrf (.imp ph (.classMem X A))) :
    Nominal.NPrf (.imp ph (syn_wbr X R X)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (X).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_wbr X R X)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eleq2d ph (syn_cdm R) A X hyp_erref_2
  have p0001 :=
    @g_eldm y X R dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_adantr ph (syn_wbr R (syn_cer) (syn_cvv)) (syn_wbr X R (.cv y)) hyp_erref_1
  have p0003 :=
    @g_elex X A
  have p0004 :=
    @g_syl ph (.classMem X A) (.classMem X (syn_cvv)) hyp_erref_3 p0003
  have p0005 :=
    @g_adantr ph (.classMem X (syn_cvv)) (syn_wbr X R (.cv y)) p0004
  have p0006 :=
    @g_vex y
  have p0007 :=
    @g_a1i (.classMem (.cv y) (syn_cvv)) (syn_wa ph (syn_wbr X R (.cv y))) p0006
  have p0008 :=
    @g_simpr ph (syn_wbr X R (.cv y))
  have p0009 :=
    @g_ertr4d (syn_wa ph (syn_wbr X R (.cv y))) (syn_cvv) R X (.cv y) X p0002 p0005 p0007 p0005 p0008 p0008
  have p0010 :=
    @g_ex ph (syn_wbr X R (.cv y)) (syn_wbr X R X) p0009
  have p0011 :=
    @g_exlimdv ph (syn_wbr X R (.cv y)) (syn_wbr X R X) y dv_cache_0003 dv_cache_0004 p0010
  have p0012 :=
    @g_syl5bi (.classMem X (syn_cdm R)) (syn_wex y (syn_wbr X R (.cv y))) ph (syn_wbr X R X) p0001 p0011
  have p0013 :=
    @g_sylbird ph (.classMem X A) (.classMem X (syn_cdm R)) (syn_wbr X R X) p0000 p0012
  have p0014 :=
    @g_mpd ph (.classMem X A) (syn_wbr X R X) hyp_erref_3 p0013
  exact p0014

noncomputable def g_eceq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cec A C) (syn_cec B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_sneq A B
  have p0001 :=
    @g_imaeq2d (.classEq A B) (syn_csn A) (syn_csn B) C p0000
  have p0002 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec A C)))
  have p0003 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec B C)))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cima C (syn_csn A)) (syn_cima C (syn_csn B)) (syn_cec A C) (syn_cec B C) p0001 p0002 p0003
  exact p0004

noncomputable def g_eceq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cec C A) (syn_cec C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_imaeq1 A B (syn_csn C)
  have p0001 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec C A)))
  have p0002 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec C B)))
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cima A (syn_csn C)) (syn_cima B (syn_csn C)) (syn_cec C A) (syn_cec C B) p0000 p0001 p0002
  exact p0003

noncomputable def g_elec
    (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cec B R)) (syn_wbr B R A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    @g_elimasn R B A
  have p0001 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec B R)))
  have p0002 :=
    @g_eleq2i (syn_cec B R) (syn_cima R (syn_csn B)) A p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr B R A)))
  have p0004 :=
    @g_n_3bitr4i (.classMem A (syn_cima R (syn_csn B))) (.classMem (syn_cop B A) R) (.classMem A (syn_cec B R)) (syn_wbr B R A) p0000 p0002 p0003
  exact p0004

noncomputable def g_erdmrn
    (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cdm R) (syn_crn R))) := by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((syn_wbr R (syn_cer) (syn_cvv))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cer, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cdm R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_crn R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wbr R (syn_cer) (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cer, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wbr R (syn_cer) (syn_cvv))
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) (syn_wbr R (syn_cer) (syn_cvv)) p0001
  have p0003 :=
    @g_vex y
  have p0004 :=
    @g_a1i (.classMem (.cv y) (syn_cvv)) (syn_wbr R (syn_cer) (syn_cvv)) p0003
  have p0005 :=
    @g_ersymb (syn_wbr R (syn_cer) (syn_cvv)) (syn_cvv) R (.cv x) (.cv y) p0000 p0002 p0004
  have p0006 :=
    @g_exbidv (syn_wbr R (syn_cer) (syn_cvv)) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)) y dv_cache_0001 p0005
  have p0007 :=
    @g_eldm y (.cv x) R dv_cache_0002 dv_cache_0003
  have p0008 :=
    @g_elrn y (.cv x) R dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_n_3bitr4g (syn_wbr R (syn_cer) (syn_cvv)) (syn_wex y (syn_wbr (.cv x) R (.cv y))) (syn_wex y (syn_wbr (.cv y) R (.cv x))) (.classMem (.cv x) (syn_cdm R)) (.classMem (.cv x) (syn_crn R)) p0006 p0007 p0008
  have p0010 :=
    @g_eqrdv (syn_wbr R (syn_cer) (syn_cvv)) x (syn_cdm R) (syn_crn R) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0009
  exact p0010

noncomputable def g_ecss
    (ph : Wff) (A : Class) (R : Class) (X : Class) (hyp_ecss_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv)))) (hyp_ecss_2 : Nominal.NPrf (.imp ph (.classEq (syn_cdm R) X))) :
    Nominal.NPrf (.imp ph (syn_wss (syn_cec A R) X)) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv
  have p0000 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec A R)))
  have p0001 :=
    @g_imassrn R (syn_csn A)
  have p0002 :=
    @g_eqsstri (syn_cec A R) (syn_cima R (syn_csn A)) (syn_crn R) p0000 p0001
  have p0003 :=
    @g_erdmrn R
  have p0004 :=
    @g_syl ph (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cdm R) (syn_crn R)) hyp_ecss_1 p0003
  have p0005 :=
    @g_eqtr3d ph (syn_cdm R) (syn_crn R) X p0004 hyp_ecss_2
  have p0006 :=
    @g_syl5sseq ph (syn_crn R) (syn_cec A R) X p0002 p0005
  exact p0006

noncomputable def g_ecdmn0
    (A : Class) (R : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cdm R)) (syn_wne (syn_cec A R) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_cec A R)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elec (.cv x) A R
  have p0001 :=
    @g_exbii (.classMem (.cv x) (syn_cec A R)) (syn_wbr A R (.cv x)) x p0000
  have p0002 :=
    @g_n0 x (syn_cec A R) dv_cache_0001
  have p0003 :=
    @g_eldm x A R dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_n_3bitr4ri (syn_wex x (.classMem (.cv x) (syn_cec A R))) (syn_wex x (syn_wbr A R (.cv x))) (syn_wne (syn_cec A R) (syn_c0)) (.classMem A (syn_cdm R)) p0001 p0002 p0003
  exact p0004

#print axioms g_ecdmn0

end NFChoice.DirectNominalPrf.WPPReplay
