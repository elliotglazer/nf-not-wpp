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
import NominalWPPReplayChunk013Compact001Part042

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

noncomputable def g_elncs
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have dv_cache_0001 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cen)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cncs] using (Nominal.classEqRefl (syn_cncs)))
  have p0001 :=
    @g_eleq2i (syn_cncs) (syn_cqs (syn_cvv) (syn_cen)) A p0000
  have p0002 :=
    @g_elex A (syn_cqs (syn_cvv) (syn_cen))
  have p0003 :=
    @g_ncex (.cv x)
  have p0004 :=
    @g_eleq1 A (syn_cnc (.cv x)) (syn_cvv)
  have p0005 :=
    @g_mpbiri (.classEq A (syn_cnc (.cv x))) (.classMem A (syn_cvv)) (.classMem (syn_cnc (.cv x)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_exlimiv (.classEq A (syn_cnc (.cv x))) (.classMem A (syn_cvv)) x dv_cache_0001 p0005
  have p0007 :=
    @g_elqsg x (syn_cvv) A (syn_cen) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0008 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc (.cv x))))
  have p0009 :=
    @g_eqeq2i (syn_cnc (.cv x)) (syn_cec (.cv x) (syn_cen)) A p0008
  have p0010 :=
    @g_exbii (.classEq A (syn_cnc (.cv x))) (.classEq A (syn_cec (.cv x) (syn_cen))) x p0009
  have p0011 :=
    @g_rexv (.classEq A (syn_cec (.cv x) (syn_cen))) x
  have p0012 :=
    @g_bitr4i (syn_wex x (.classEq A (syn_cnc (.cv x)))) (syn_wex x (.classEq A (syn_cec (.cv x) (syn_cen)))) (syn_wrex x (syn_cvv) (.classEq A (syn_cec (.cv x) (syn_cen)))) p0010 p0011
  have p0013 :=
    @g_syl6bbr (.classMem A (syn_cvv)) (.classMem A (syn_cqs (syn_cvv) (syn_cen))) (syn_wrex x (syn_cvv) (.classEq A (syn_cec (.cv x) (syn_cen)))) (syn_wex x (.classEq A (syn_cnc (.cv x)))) p0007 p0012
  have p0014 :=
    @g_pm5_21nii (.classMem A (syn_cqs (syn_cvv) (syn_cen))) (.classMem A (syn_cvv)) (syn_wex x (.classEq A (syn_cnc (.cv x)))) p0002 p0006 p0013
  have p0015 :=
    @g_bitri (.classMem A (syn_cncs)) (.classMem A (syn_cqs (syn_cvv) (syn_cen))) (syn_wex x (.classEq A (syn_cnc (.cv x)))) p0001 p0014
  exact p0015

noncomputable def g_ncelncs
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cnc A) (syn_cncs))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elisset x A V dv_cache_0001
  have p0001 :=
    @g_nceq A (.cv x)
  have p0002 :=
    @g_eqcoms (.classEq (syn_cnc A) (syn_cnc (.cv x))) A (.cv x) p0001
  have p0003 :=
    @g_eximi (.classEq (.cv x) A) (.classEq (syn_cnc A) (syn_cnc (.cv x))) x p0002
  have p0004 :=
    @g_syl (.classMem A V) (syn_wex x (.classEq (.cv x) A)) (syn_wex x (.classEq (syn_cnc A) (syn_cnc (.cv x)))) p0000 p0003
  have p0005 :=
    @g_elncs x (syn_cnc A) dv_cache_0002
  have p0006 :=
    @g_sylibr (.classMem A V) (syn_wex x (.classEq (syn_cnc A) (syn_cnc (.cv x)))) (.classMem (syn_cnc A) (syn_cncs)) p0004 p0005
  exact p0006

noncomputable def g_ncelncsi
    (A : Class) (hyp_ncelncsi_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cnc A) (syn_cncs)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ncelncs A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_ncelncsi_1 p0000
  exact p0001

noncomputable def g_ncidg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem A (syn_cnc A))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_enrflxg A V
  have p0001 :=
    @g_elec A A (syn_cen)
  have p0002 :=
    @g_sylibr (.classMem A V) (syn_wbr A (syn_cen) A) (.classMem A (syn_cec A (syn_cen))) p0000 p0001
  have p0003 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc A)))
  have p0004 :=
    @g_syl6eleqr (.classMem A V) A (syn_cec A (syn_cen)) (syn_cnc A) p0002 p0003
  exact p0004

noncomputable def g_ncid
    (A : Class) (hyp_ncid_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem A (syn_cnc A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ncidg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_ncid_1 p0000
  exact p0001

noncomputable def g_elnc
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cnc B)) (syn_wbr A (syn_cen) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_elex A (syn_cnc B)
  have p0001 :=
    @g_ecexr A B (syn_cen)
  have p0002 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc B)))
  have p0003 :=
    @g_eleq2s (.classMem B (syn_cvv)) A (syn_cec B (syn_cen)) (syn_cnc B) p0001 p0002
  have p0004 :=
    @g_jca (.classMem A (syn_cnc B)) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0000 p0003
  have p0005 :=
    @g_brex A B (syn_cen)
  have p0006 :=
    @g_eleq2i (syn_cnc B) (syn_cec B (syn_cen)) A p0002
  have p0007 :=
    @g_elec A B (syn_cen)
  have p0008 :=
    @g_bitri (.classMem A (syn_cnc B)) (.classMem A (syn_cec B (syn_cen))) (syn_wbr B (syn_cen) A) p0006 p0007
  have p0009 :=
    @g_ener
  have p0010 :=
    @g_a1i (syn_wbr (syn_cen) (syn_cer) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0009
  have p0011 :=
    @g_simpr (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
  have p0012 :=
    @g_simpl (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
  have p0013 :=
    @g_ersymb (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_cvv) (syn_cen) B A p0010 p0011 p0012
  have p0014 :=
    @g_syl5bb (.classMem A (syn_cnc B)) (syn_wbr B (syn_cen) A) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr A (syn_cen) B) p0008 p0013
  have p0015 :=
    @g_pm5_21nii (.classMem A (syn_cnc B)) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr A (syn_cen) B) p0004 p0005 p0014
  exact p0015

noncomputable def g_eqncg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  have p0000 :=
    @g_ncidg A V
  have p0001 :=
    @g_adantr (.classMem A V) (.classMem A (syn_cnc A)) (.classEq (syn_cnc A) (syn_cnc B)) p0000
  have p0002 :=
    @g_eleq2 (syn_cnc A) (syn_cnc B) A
  have p0003 :=
    @g_adantl (.classEq (syn_cnc A) (syn_cnc B)) (syn_wb (.classMem A (syn_cnc A)) (.classMem A (syn_cnc B))) (.classMem A V) p0002
  have p0004 :=
    @g_mpbid (syn_wa (.classMem A V) (.classEq (syn_cnc A) (syn_cnc B))) (.classMem A (syn_cnc A)) (.classMem A (syn_cnc B)) p0001 p0003
  have p0005 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc B)))
  have p0006 :=
    @g_syl6eleq (syn_wa (.classMem A V) (.classEq (syn_cnc A) (syn_cnc B))) A (syn_cnc B) (syn_cec B (syn_cen)) p0004 p0005
  have p0007 :=
    @g_ecexr A B (syn_cen)
  have p0008 :=
    @g_syl (syn_wa (.classMem A V) (.classEq (syn_cnc A) (syn_cnc B))) (.classMem A (syn_cec B (syn_cen))) (.classMem B (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_ex (.classMem A V) (.classEq (syn_cnc A) (syn_cnc B)) (.classMem B (syn_cvv)) p0008
  have p0010 :=
    @g_brex A B (syn_cen)
  have p0011 :=
    @g_simprd (syn_wbr A (syn_cen) B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0010
  have p0012 :=
    @g_a1i (.imp (syn_wbr A (syn_cen) B) (.classMem B (syn_cvv))) (.classMem A V) p0011
  have p0013 :=
    @g_ener
  have p0014 :=
    @g_a1i (syn_wbr (syn_cen) (syn_cer) (syn_cvv)) (syn_wa (.classMem A V) (.classMem B (syn_cvv))) p0013
  have p0015 :=
    @g_dmen
  have p0016 :=
    @g_a1i (.classEq (syn_cdm (syn_cen)) (syn_cvv)) (syn_wa (.classMem A V) (.classMem B (syn_cvv))) p0015
  have p0017 :=
    @g_elex A V
  have p0018 :=
    @g_adantr (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0017
  have p0019 :=
    @g_simpr (.classMem A V) (.classMem B (syn_cvv))
  have p0020 :=
    @g_erth (syn_wa (.classMem A V) (.classMem B (syn_cvv))) A B (syn_cen) (syn_cvv) (syn_cvv) p0014 p0016 p0018 p0019
  have p0021 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc A)))
  have p0022 :=
    @g_eqeq12i (syn_cnc A) (syn_cec A (syn_cen)) (syn_cnc B) (syn_cec B (syn_cen)) p0021 p0005
  have p0023 :=
    @g_syl6rbbr (syn_wa (.classMem A V) (.classMem B (syn_cvv))) (syn_wbr A (syn_cen) B) (.classEq (syn_cec A (syn_cen)) (syn_cec B (syn_cen))) (.classEq (syn_cnc A) (syn_cnc B)) p0020 p0022
  have p0024 :=
    @g_ex (.classMem A V) (.classMem B (syn_cvv)) (syn_wb (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B)) p0023
  have p0025 :=
    @g_pm5_21ndd (.classMem A V) (.classMem B (syn_cvv)) (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B) p0009 p0012 p0024
  exact p0025

noncomputable def g_eqnc
    (A : Class) (B : Class) (hyp_eqnc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_eqncg A B (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_eqnc_1 p0000
  exact p0001

noncomputable def g_ncseqnc
    (A : Class) (X : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cncs)) (syn_wb (.classEq A (syn_cnc X)) (.classMem X A))) := by
  let proofSupport : Finset Var := A.fv ∪ X.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wb (.classEq A (syn_cnc X)) (.classMem X A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs y A dv_cache_0001
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_ncid (.cv y) p0001
  have p0003 :=
    @g_eleq2 (syn_cnc X) (syn_cnc (.cv y)) (.cv y)
  have p0004 :=
    @g_mpbiri (.classEq (syn_cnc X) (syn_cnc (.cv y))) (.classMem (.cv y) (syn_cnc X)) (.classMem (.cv y) (syn_cnc (.cv y))) p0002 p0003
  have p0005 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc X)))
  have p0006 :=
    @g_syl6eleq (.classEq (syn_cnc X) (syn_cnc (.cv y))) (.cv y) (syn_cnc X) (syn_cec X (syn_cen)) p0004 p0005
  have p0007 :=
    @g_ecexr (.cv y) X (syn_cen)
  have p0008 :=
    @g_syl (.classEq (syn_cnc X) (syn_cnc (.cv y))) (.classMem (.cv y) (syn_cec X (syn_cen))) (.classMem X (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_brex X (.cv y) (syn_cen)
  have p0010 :=
    @g_simpld (syn_wbr X (syn_cen) (.cv y)) (.classMem X (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0009
  have p0011 :=
    @g_ener
  have p0012 :=
    @g_a1i (syn_wbr (syn_cen) (syn_cer) (syn_cvv)) (.classMem X (syn_cvv)) p0011
  have p0013 :=
    @g_dmen
  have p0014 :=
    @g_a1i (.classEq (syn_cdm (syn_cen)) (syn_cvv)) (.classMem X (syn_cvv)) p0013
  have p0015 :=
    @g_id (.classMem X (syn_cvv))
  have p0016 :=
    @g_a1i (.classMem (.cv y) (syn_cvv)) (.classMem X (syn_cvv)) p0001
  have p0017 :=
    @g_erth (.classMem X (syn_cvv)) X (.cv y) (syn_cen) (syn_cvv) (syn_cvv) p0012 p0014 p0015 p0016
  have p0018 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc (.cv y))))
  have p0019 :=
    @g_eqeq12i (syn_cnc X) (syn_cec X (syn_cen)) (syn_cnc (.cv y)) (syn_cec (.cv y) (syn_cen)) p0005 p0018
  have p0020 :=
    @g_syl6rbbr (.classMem X (syn_cvv)) (syn_wbr X (syn_cen) (.cv y)) (.classEq (syn_cec X (syn_cen)) (syn_cec (.cv y) (syn_cen))) (.classEq (syn_cnc X) (syn_cnc (.cv y))) p0017 p0019
  have p0021 :=
    @g_pm5_21nii (.classEq (syn_cnc X) (syn_cnc (.cv y))) (.classMem X (syn_cvv)) (syn_wbr X (syn_cen) (.cv y)) p0008 p0010 p0020
  have p0022 :=
    @g_eqcom (syn_cnc (.cv y)) (syn_cnc X)
  have p0023 :=
    @g_elnc X (.cv y)
  have p0024 :=
    @g_n_3bitr4i (.classEq (syn_cnc X) (syn_cnc (.cv y))) (syn_wbr X (syn_cen) (.cv y)) (.classEq (syn_cnc (.cv y)) (syn_cnc X)) (.classMem X (syn_cnc (.cv y))) p0021 p0022 p0023
  have p0025 :=
    @g_a1i (syn_wb (.classEq (syn_cnc (.cv y)) (syn_cnc X)) (.classMem X (syn_cnc (.cv y)))) (.classEq A (syn_cnc (.cv y))) p0024
  have p0026 :=
    @g_eqeq1 A (syn_cnc (.cv y)) (syn_cnc X)
  have p0027 :=
    @g_eleq2 A (syn_cnc (.cv y)) X
  have p0028 :=
    @g_n_3bitr4d (.classEq A (syn_cnc (.cv y))) (.classEq (syn_cnc (.cv y)) (syn_cnc X)) (.classMem X (syn_cnc (.cv y))) (.classEq A (syn_cnc X)) (.classMem X A) p0025 p0026 p0027
  have p0029 :=
    @g_exlimiv (.classEq A (syn_cnc (.cv y))) (syn_wb (.classEq A (syn_cnc X)) (.classMem X A)) y dv_cache_0002 p0028
  have p0030 :=
    @g_sylbi (.classMem A (syn_cncs)) (syn_wex y (.classEq A (syn_cnc (.cv y)))) (syn_wb (.classEq A (syn_cnc X)) (.classMem X A)) p0000 p0029
  exact p0030

#print axioms g_ncseqnc

end NFChoice.DirectNominalPrf.WPPReplay
