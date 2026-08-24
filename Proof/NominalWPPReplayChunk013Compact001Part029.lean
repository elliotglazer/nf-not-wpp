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
import NominalWPPReplayChunk013Compact001Part028

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

noncomputable def g_erth
    (ph : Wff) (A : Class) (B : Class) (R : Class) (V : Class) (X : Class) (hyp_erth_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv)))) (hyp_erth_2 : Nominal.NPrf (.imp ph (.classEq (syn_cdm R) X))) (hyp_erth_3 : Nominal.NPrf (.imp ph (.classMem A X))) (hyp_erth_4 : Nominal.NPrf (.imp ph (.classMem B V))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wbr A R B) (.classEq (syn_cec A R) (syn_cec B R)))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ R.fv ∪ V.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_wa ph (syn_wbr A R B))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_ph, fresh_x_not_A, fresh_x_not_B, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_adantr ph (syn_wbr R (syn_cer) (syn_cvv)) (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x))) hyp_erth_1
  have p0001 :=
    @g_elex B V
  have p0002 :=
    @g_syl ph (.classMem B V) (.classMem B (syn_cvv)) hyp_erth_4 p0001
  have p0003 :=
    @g_adantr ph (.classMem B (syn_cvv)) (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x))) p0002
  have p0004 :=
    @g_elex A X
  have p0005 :=
    @g_syl ph (.classMem A X) (.classMem A (syn_cvv)) hyp_erth_3 p0004
  have p0006 :=
    @g_adantr ph (.classMem A (syn_cvv)) (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x))) p0005
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) (syn_wa ph (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x)))) p0007
  have p0009 :=
    @g_simprl ph (syn_wbr A R B) (syn_wbr A R (.cv x))
  have p0010 :=
    @g_simprr ph (syn_wbr A R B) (syn_wbr A R (.cv x))
  have p0011 :=
    @g_ertr3d (syn_wa ph (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x)))) (syn_cvv) R B A (.cv x) p0000 p0003 p0006 p0008 p0009 p0010
  have p0012 :=
    @g_expr ph (syn_wbr A R B) (syn_wbr A R (.cv x)) (syn_wbr B R (.cv x)) p0011
  have p0013 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) ph p0007
  have p0014 :=
    @g_ertr ph (syn_cvv) R A B (.cv x) hyp_erth_1 p0005 p0002 p0013
  have p0015 :=
    @g_expdimp ph (syn_wbr A R B) (syn_wbr B R (.cv x)) (syn_wbr A R (.cv x)) p0014
  have p0016 :=
    @g_impbid (syn_wa ph (syn_wbr A R B)) (syn_wbr A R (.cv x)) (syn_wbr B R (.cv x)) p0012 p0015
  have p0017 :=
    @g_abbidv (syn_wa ph (syn_wbr A R B)) (syn_wbr A R (.cv x)) (syn_wbr B R (.cv x)) x dv_cache_0001 p0016
  have p0018 :=
    @g_dfec2 x A R dv_cache_0002 dv_cache_0003
  have p0019 :=
    @g_dfec2 x B R dv_cache_0004 dv_cache_0003
  have p0020 :=
    @g_n_3eqtr4g (syn_wa ph (syn_wbr A R B)) (.cab x (syn_wbr A R (.cv x))) (.cab x (syn_wbr B R (.cv x))) (syn_cec A R) (syn_cec B R) p0017 p0018 p0019
  have p0021 :=
    @g_adantr ph (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cec A R) (syn_cec B R)) hyp_erth_1
  have p0022 :=
    @g_simpl ph (.classEq (syn_cec A R) (syn_cec B R))
  have p0023 :=
    @g_n_3syl (syn_wa ph (.classEq (syn_cec A R) (syn_cec B R))) ph (.classMem B V) (.classMem B (syn_cvv)) p0022 hyp_erth_4 p0001
  have p0024 :=
    @g_n_3syl (syn_wa ph (.classEq (syn_cec A R) (syn_cec B R))) ph (.classMem A X) (.classMem A (syn_cvv)) p0022 hyp_erth_3 p0004
  have p0025 :=
    @g_erref ph X R A hyp_erth_1 hyp_erth_2 hyp_erth_3
  have p0026 :=
    @g_elec A A R
  have p0027 :=
    @g_sylibr ph (syn_wbr A R A) (.classMem A (syn_cec A R)) p0025 p0026
  have p0028 :=
    @g_eleq2 (syn_cec A R) (syn_cec B R) A
  have p0029 :=
    @g_syl5ibcom ph (.classMem A (syn_cec A R)) (.classEq (syn_cec A R) (syn_cec B R)) (.classMem A (syn_cec B R)) p0027 p0028
  have p0030 :=
    @g_imp ph (.classEq (syn_cec A R) (syn_cec B R)) (.classMem A (syn_cec B R)) p0029
  have p0031 :=
    @g_elec A B R
  have p0032 :=
    @g_sylib (syn_wa ph (.classEq (syn_cec A R) (syn_cec B R))) (.classMem A (syn_cec B R)) (syn_wbr B R A) p0030 p0031
  have p0033 :=
    @g_ersym (syn_wa ph (.classEq (syn_cec A R) (syn_cec B R))) (syn_cvv) R B A p0021 p0023 p0024 p0032
  have p0034 :=
    @g_impbida ph (syn_wbr A R B) (.classEq (syn_cec A R) (syn_cec B R)) p0020 p0033
  exact p0034

noncomputable def g_erth2
    (ph : Wff) (A : Class) (B : Class) (R : Class) (V : Class) (X : Class) (hyp_erth2_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv)))) (hyp_erth2_2 : Nominal.NPrf (.imp ph (.classEq (syn_cdm R) X))) (hyp_erth2_3 : Nominal.NPrf (.imp ph (.classMem A V))) (hyp_erth2_4 : Nominal.NPrf (.imp ph (.classMem B X))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wbr A R B) (.classEq (syn_cec A R) (syn_cec B R)))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ R.fv ∪ V.fv ∪ X.fv
  have p0000 :=
    @g_elex A V
  have p0001 :=
    @g_syl ph (.classMem A V) (.classMem A (syn_cvv)) hyp_erth2_3 p0000
  have p0002 :=
    @g_elex B X
  have p0003 :=
    @g_syl ph (.classMem B X) (.classMem B (syn_cvv)) hyp_erth2_4 p0002
  have p0004 :=
    @g_ersymb ph (syn_cvv) R A B hyp_erth2_1 p0001 p0003
  have p0005 :=
    @g_erth ph B A R V X hyp_erth2_1 hyp_erth2_2 hyp_erth2_4 hyp_erth2_3
  have p0006 :=
    @g_eqcom (syn_cec B R) (syn_cec A R)
  have p0007 :=
    @g_syl6bb ph (syn_wbr B R A) (.classEq (syn_cec B R) (syn_cec A R)) (.classEq (syn_cec A R) (syn_cec B R)) p0005 p0006
  have p0008 :=
    @g_bitrd ph (syn_wbr A R B) (syn_wbr B R A) (.classEq (syn_cec A R) (syn_cec B R)) p0004 p0007
  exact p0008

noncomputable def g_erthi
    (ph : Wff) (A : Class) (B : Class) (R : Class) (hyp_erthi_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv)))) (hyp_erthi_4 : Nominal.NPrf (.imp ph (syn_wbr A R B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cec A R) (syn_cec B R))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    @g_eqidd ph (syn_cdm R)
  have p0001 :=
    @g_breldm A B R
  have p0002 :=
    @g_syl ph (syn_wbr A R B) (.classMem A (syn_cdm R)) hyp_erthi_4 p0001
  have p0003 :=
    @g_brelrn A B R
  have p0004 :=
    @g_syl ph (syn_wbr A R B) (.classMem B (syn_crn R)) hyp_erthi_4 p0003
  have p0005 :=
    @g_erth ph A B R (syn_crn R) (syn_cdm R) hyp_erthi_1 p0000 p0002 p0004
  have p0006 :=
    @g_mpbid ph (syn_wbr A R B) (.classEq (syn_cec A R) (syn_cec B R)) hyp_erthi_4 p0005
  exact p0006

noncomputable def g_erdisj
    (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cer) (syn_cvv)) (syn_wo (.classEq (syn_cec A R) (syn_cec B R)) (.classEq (syn_cin (syn_cec A R) (syn_cec B R)) (syn_c0)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_cin (syn_cec A R) (syn_cec B R))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_R, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (syn_cec A R) (syn_cec B R))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_R, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_wbr R (syn_cer) (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cer, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_neq0 x (syn_cin (syn_cec A R) (syn_cec B R)) dv_cache_0001
  have p0001 :=
    @g_simpl (syn_wbr R (syn_cer) (syn_cvv)) (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
  have p0002 :=
    @g_inss1 (syn_cec A R) (syn_cec B R)
  have p0003 :=
    @g_sseli (syn_cin (syn_cec A R) (syn_cec B R)) (syn_cec A R) (.cv x) p0002
  have p0004 :=
    @g_adantl (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))) (.classMem (.cv x) (syn_cec A R)) (syn_wbr R (syn_cer) (syn_cvv)) p0003
  have p0005 :=
    @g_ecexr (.cv x) A R
  have p0006 :=
    @g_syl (syn_wa (syn_wbr R (syn_cer) (syn_cvv)) (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))) (.classMem (.cv x) (syn_cec A R)) (.classMem A (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) (syn_wa (syn_wbr R (syn_cer) (syn_cvv)) (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))) p0007
  have p0009 :=
    @g_inss2 (syn_cec A R) (syn_cec B R)
  have p0010 :=
    @g_sseli (syn_cin (syn_cec A R) (syn_cec B R)) (syn_cec B R) (.cv x) p0009
  have p0011 :=
    @g_adantl (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))) (.classMem (.cv x) (syn_cec B R)) (syn_wbr R (syn_cer) (syn_cvv)) p0010
  have p0012 :=
    @g_ecexr (.cv x) B R
  have p0013 :=
    @g_syl (syn_wa (syn_wbr R (syn_cer) (syn_cvv)) (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))) (.classMem (.cv x) (syn_cec B R)) (.classMem B (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_elec (.cv x) A R
  have p0015 :=
    @g_sylib (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))) (.classMem (.cv x) (syn_cec A R)) (syn_wbr A R (.cv x)) p0003 p0014
  have p0016 :=
    @g_adantl (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))) (syn_wbr A R (.cv x)) (syn_wbr R (syn_cer) (syn_cvv)) p0015
  have p0017 :=
    @g_elec (.cv x) B R
  have p0018 :=
    @g_sylib (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))) (.classMem (.cv x) (syn_cec B R)) (syn_wbr B R (.cv x)) p0010 p0017
  have p0019 :=
    @g_adantl (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))) (syn_wbr B R (.cv x)) (syn_wbr R (syn_cer) (syn_cvv)) p0018
  have p0020 :=
    @g_ertr4d (syn_wa (syn_wbr R (syn_cer) (syn_cvv)) (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))) (syn_cvv) R A (.cv x) B p0001 p0006 p0008 p0013 p0016 p0019
  have p0021 :=
    @g_erthi (syn_wa (syn_wbr R (syn_cer) (syn_cvv)) (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))) A B R p0001 p0020
  have p0022 :=
    @g_ex (syn_wbr R (syn_cer) (syn_cvv)) (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))) (.classEq (syn_cec A R) (syn_cec B R)) p0021
  have p0023 :=
    @g_exlimdv (syn_wbr R (syn_cer) (syn_cvv)) (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))) (.classEq (syn_cec A R) (syn_cec B R)) x dv_cache_0002 dv_cache_0003 p0022
  have p0024 :=
    @g_syl5bi (.neg (.classEq (syn_cin (syn_cec A R) (syn_cec B R)) (syn_c0))) (syn_wex x (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))) (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cec A R) (syn_cec B R)) p0000 p0023
  have p0025 :=
    @g_orrd (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cin (syn_cec A R) (syn_cec B R)) (syn_c0)) (.classEq (syn_cec A R) (syn_cec B R)) p0024
  have p0026 :=
    @g_orcomd (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cin (syn_cec A R) (syn_cec B R)) (syn_c0)) (.classEq (syn_cec A R) (syn_cec B R)) p0025
  exact p0026

noncomputable def g_qseq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cqs A C) (syn_cqs B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_rexeq (.classEq (.cv y) (syn_cec (.cv x) C)) x A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wrex x A (.classEq (.cv y) (syn_cec (.cv x) C))) (syn_wrex x B (.classEq (.cv y) (syn_cec (.cv x) C))) y dv_cache_0003 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y A C dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y B C dv_cache_0002 dv_cache_0008 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cec (.cv x) C)))) (.cab y (syn_wrex x B (.classEq (.cv y) (syn_cec (.cv x) C)))) (syn_cqs A C) (syn_cqs B C) p0001 p0002 p0003
  exact p0004

noncomputable def g_qseq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cqs C A) (syn_cqs C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((Wff.classEq A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eceq2 A B (.cv x)
  have p0001 :=
    @g_eqeq2d (.classEq A B) (syn_cec (.cv x) A) (syn_cec (.cv x) B) (.cv y) p0000
  have p0002 :=
    @g_rexbidv (.classEq A B) (.classEq (.cv y) (syn_cec (.cv x) A)) (.classEq (.cv y) (syn_cec (.cv x) B)) x C dv_cache_0001 p0001
  have p0003 :=
    @g_abbidv (.classEq A B) (syn_wrex x C (.classEq (.cv y) (syn_cec (.cv x) A))) (syn_wrex x C (.classEq (.cv y) (syn_cec (.cv x) B))) y dv_cache_0002 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y C A dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y C B dv_cache_0003 dv_cache_0004 dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0006 :=
    @g_n_3eqtr4g (.classEq A B) (.cab y (syn_wrex x C (.classEq (.cv y) (syn_cec (.cv x) A)))) (.cab y (syn_wrex x C (.classEq (.cv y) (syn_cec (.cv x) B)))) (syn_cqs C A) (syn_cqs C B) p0003 p0004 p0005
  exact p0006

noncomputable def g_elqsg
    (x : Var) (A : Class) (B : Class) (R : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf (.imp (.classMem B V) (syn_wb (.classMem B (syn_cqs A R)) (syn_wrex x A (.classEq B (syn_cec (.cv x) R))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wrex x A (.classEq B (syn_cec (.cv x) R)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqeq1 (.cv y) B (syn_cec (.cv x) R)
  have p0001 :=
    @g_rexbidv (.classEq (.cv y) B) (.classEq (.cv y) (syn_cec (.cv x) R)) (.classEq B (syn_cec (.cv x) R)) x A dv_cache_0001 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y A R dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    @g_elab2g (syn_wrex x A (.classEq (.cv y) (syn_cec (.cv x) R))) (syn_wrex x A (.classEq B (syn_cec (.cv x) R))) y B (syn_cqs A R) V dv_cache_0007 dv_cache_0008 p0001 p0002
  exact p0003

noncomputable def g_elqs
    (x : Var) (A : Class) (B : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) (hyp_elqs_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem B (syn_cqs A R)) (syn_wrex x A (.classEq B (syn_cec (.cv x) R)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elqsg x A B R (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    Nominal.mp hyp_elqs_1 p0000
  exact p0001

noncomputable def g_elqsi
    (x : Var) (A : Class) (B : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf (.imp (.classMem B (syn_cqs A R)) (syn_wrex x A (.classEq B (syn_cec (.cv x) R)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elqsg x A B R (syn_cqs A R) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_ibi (.classMem B (syn_cqs A R)) (syn_wrex x A (.classEq B (syn_cec (.cv x) R))) p0000
  exact p0001

noncomputable def g_ecelqsg
    (A : Class) (B : Class) (R : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem R V) (.classMem B A)) (.classMem (syn_cec B R) (syn_cqs A R))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (syn_cec B R) (syn_cec B R))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cec B R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqid (syn_cec B R)
  have p0001 :=
    @g_eceq1 (.cv x) B R
  have p0002 :=
    @g_eqeq2d (.classEq (.cv x) B) (syn_cec (.cv x) R) (syn_cec B R) (syn_cec B R) p0001
  have p0003 :=
    @g_rspcev (.classEq (syn_cec B R) (syn_cec (.cv x) R)) (.classEq (syn_cec B R) (syn_cec B R)) x B A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0002
  have p0004 :=
    @g_mpan2 (.classMem B A) (.classEq (syn_cec B R) (syn_cec B R)) (syn_wrex x A (.classEq (syn_cec B R) (syn_cec (.cv x) R))) p0000 p0003
  have p0005 :=
    @g_ecexg B V R
  have p0006 :=
    @g_elqsg x A (syn_cec B R) R (syn_cvv) dv_cache_0002 dv_cache_0004 dv_cache_0005
  have p0007 :=
    @g_syl (.classMem R V) (.classMem (syn_cec B R) (syn_cvv)) (syn_wb (.classMem (syn_cec B R) (syn_cqs A R)) (syn_wrex x A (.classEq (syn_cec B R) (syn_cec (.cv x) R)))) p0005 p0006
  have p0008 :=
    @g_biimpar (.classMem R V) (.classMem (syn_cec B R) (syn_cqs A R)) (syn_wrex x A (.classEq (syn_cec B R) (syn_cec (.cv x) R))) p0007
  have p0009 :=
    @g_sylan2 (.classMem B A) (.classMem R V) (syn_wrex x A (.classEq (syn_cec B R) (syn_cec (.cv x) R))) (.classMem (syn_cec B R) (syn_cqs A R)) p0004 p0008
  exact p0009

noncomputable def g_ecelqsi
    (A : Class) (B : Class) (R : Class) (hyp_ecelqsi_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B A) (.classMem (syn_cec B R) (syn_cqs A R))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    @g_ecelqsg A B R (syn_cvv)
  have p0001 :=
    @g_mpan (.classMem R (syn_cvv)) (.classMem B A) (.classMem (syn_cec B R) (syn_cqs A R)) hyp_ecelqsi_1 p0000
  exact p0001

#print axioms g_ecelqsi

end NFChoice.DirectNominalPrf.WPPReplay
