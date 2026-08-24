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
import NominalWPPReplayChunk014Compact001Part040

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

noncomputable def g_hwnisodm
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A)) := by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have dv_cache_0001 : v ∉ ((Class.cv u)).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0004 : v ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((syn_cdm (syn_chwniso A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eldm v (.cv u) (syn_chwniso A) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_cdm (syn_chwniso A))) (syn_wex v (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) p0000
  have p0002 :=
    @g_hwnisohwisob v u A dv_cache_0003
  have p0003 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0002
  have p0004 :=
    @g_simpld (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0003
  have p0005 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0006 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0004 p0005
  have p0007 :=
    @g_exlimiv (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem (.cv u) (syn_chwcn A)) v dv_cache_0004 p0006
  have p0008 :=
    @g_syl (.classMem (.cv u) (syn_cdm (syn_chwniso A))) (syn_wex v (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcn A)) p0001 p0007
  have p0009 :=
    @g_pm4_24 (.classMem (.cv u) (syn_chwcn A))
  have p0010 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0009
  have p0011 :=
    @g_hwcnraw u A
  have p0012 :=
    @g_hwisorefl u A dv_cache_0005
  have p0013 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0011 p0012
  have p0014 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0010 p0013
  have p0015 :=
    @g_elex (.cv u) (syn_chwcn A)
  have p0016 :=
    @g_breq2 (.cv v) (.cv u) (.cv u) (syn_chwniso A)
  have p0017 :=
    @g_eleq1 (.cv v) (.cv u) (syn_chwcn A)
  have p0018 :=
    @g_anbi2d (.classEq (.cv v) (.cv u)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0017
  have p0019 :=
    @g_breq2 (.cv v) (.cv u) (.cv u) (syn_chwiso A)
  have p0020 :=
    @g_anbi12d (.classEq (.cv v) (.cv u)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0018 p0019
  have p0021 :=
    @g_bibi12d (.classEq (.cv v) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))) p0016 p0020
  have p0022 :=
    @g_hwnisohwisob v u A dv_cache_0003
  have p0023 :=
    @g_vtoclg (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))) (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)))) v (.cv u) (syn_cvv) dv_cache_0001 dv_cache_0006 p0021 p0022
  have p0024 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv)) (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)))) p0015 p0023
  have p0025 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))) p0014 p0024
  have p0026 :=
    @g_breldm (.cv u) (.cv u) (syn_chwniso A)
  have p0027 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (.classMem (.cv u) (syn_cdm (syn_chwniso A))) p0025 p0026
  have p0028 :=
    @g_impbii (.classMem (.cv u) (syn_cdm (syn_chwniso A))) (.classMem (.cv u) (syn_chwcn A)) p0008 p0027
  have p0029 :=
    @g_eqriv u (syn_cdm (syn_chwniso A)) (syn_chwcn A) dv_cache_0007 dv_cache_0008 p0028
  exact p0029

noncomputable def g_hwnisoclasseqb
    (v : Var) (u : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_simpl (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0001 :=
    @g_hwnisoerv A
  have p0002 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_hwnisodm A
  have p0004 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A)) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) p0003
  have p0005 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0006 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0005 p0006
  have p0008 :=
    @g_elex (.cv u) (syn_chwcn A)
  have p0009 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0011 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0012 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv v) (syn_chwcn A)) p0010 p0011
  have p0013 :=
    @g_erth2 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.cv u) (.cv v) (syn_chwniso A) (syn_cvv) (syn_chwcn A) p0002 p0004 p0009 p0012
  have p0014 :=
    @g_bicomd (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) p0013
  exact p0014

noncomputable def g_hnordexg
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chnord A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0001 :=
    @g_hwnisoexg A
  have p0002 :=
    @g_hwcnexg A
  have p0003 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_qsexg (syn_chwcn A) (syn_chwniso A) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chwniso A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (.classMem (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_hncardex
    (A : Class) :
    Nominal.NPrf (.classMem (syn_chncard A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard A)))
  have p0001 :=
    @g_ncex (syn_chnord A)
  have p0002 :=
    @g_eqeltri (syn_chncard A) (syn_cnc (syn_chnord A)) (syn_cvv) p0000 p0001
  exact p0002

noncomputable def g_hncardnc
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chncard A) (syn_cncs))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard A)))
  have p0001 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0002 :=
    @g_hwnisoexg A
  have p0003 :=
    @g_hwcnexg A
  have p0004 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_qsexg (syn_chwcn A) (syn_chwniso A) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chwniso A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (.classMem (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv) p0001 p0006
  have p0008 :=
    @g_ncelncs (syn_chnord A) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chnord A) (syn_cvv)) (.classMem (syn_cnc (syn_chnord A)) (syn_cncs)) p0007 p0008
  have p0010 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chncard A) (syn_cnc (syn_chnord A)) (syn_cncs) p0000 p0009
  exact p0010

noncomputable def g_hncardtc
    (A : Class) (hyp_hncardtc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_chncard A)) (syn_cnc (syn_cpw1 (syn_chnord A)))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard A)))
  have p0001 :=
    @g_tceq (syn_chncard A) (syn_cnc (syn_chnord A))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_hnordex A hyp_hncardtc_1
  have p0004 :=
    @g_tcnc (syn_chnord A) p0003
  have p0005 :=
    @g_eqtri (syn_ctc (syn_chncard A)) (syn_ctc (syn_cnc (syn_chnord A))) (syn_cnc (syn_cpw1 (syn_chnord A))) p0002 p0004
  exact p0005

noncomputable def g_hncardtc2
    (A : Class) (hyp_hncardtc2_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_chncard A))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_chnord A))))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hncardtc A hyp_hncardtc2_1
  have p0001 :=
    @g_tceq (syn_ctc (syn_chncard A)) (syn_cnc (syn_cpw1 (syn_chnord A)))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_hnordex A hyp_hncardtc2_1
  have p0004 :=
    @g_pw1ex (syn_chnord A) p0003
  have p0005 :=
    @g_tcnc (syn_cpw1 (syn_chnord A)) p0004
  have p0006 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_chncard A))) (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord A)))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_chnord A)))) p0002 p0005
  exact p0006

noncomputable def g_hwcnbase
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact (show Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (A).fv from (by exact dv_A_u)))))), (show Disjoint ((A).fv) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have p0000 :=
    @g_hwcnraw u A
  have p0001 :=
    @g_hwcnpair u A
  have p0002 :=
    @g_eleq1d (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A) p0001
  have p0003 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)) p0000 p0002
  have p0004 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0005 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0006 :=
    @g_elhwcodes A (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001 p0004 p0005
  have p0007 :=
    @g_biimpi (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) p0006
  have p0008 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) p0003 p0007
  have p0009 :=
    @g_simprd (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A) p0008
  exact p0009

noncomputable def g_elhwbases
    (u : Var) (A : Class) (D : Class) (dv_A_D : Disjoint A.fv D.fv) (dv_A_u : u ∉ A.fv) (dv_D_u : u ∉ D.fv) :
    Nominal.NPrf (syn_wb (.classMem D (syn_chwbases A)) (syn_wrex u (syn_chwcn A) (.classEq D (syn_cfv (syn_c2nd) (.cv u))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ D.fv
  have dv_cache_0001 : u ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_c2nd)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chwbases] using (Nominal.classEqRefl (syn_chwbases A)))
  have p0001 :=
    @g_eleq2i (syn_chwbases A) (syn_cima (syn_c2nd) (syn_chwcn A)) D p0000
  have p0002 :=
    @g_elima u D (syn_c2nd) (syn_chwcn A) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @g_n_2ndfo
  have p0004 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_vex u
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_fnbrfvb (syn_cvv) (.cv u) D (syn_c2nd)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_bicomi (.classEq (syn_cfv (syn_c2nd) (.cv u)) D) (syn_wbr (.cv u) (syn_c2nd) D) p0009
  have p0011 :=
    @g_eqcom (syn_cfv (syn_c2nd) (.cv u)) D
  have p0012 :=
    @g_bitri (syn_wbr (.cv u) (syn_c2nd) D) (.classEq (syn_cfv (syn_c2nd) (.cv u)) D) (.classEq D (syn_cfv (syn_c2nd) (.cv u))) p0010 p0011
  have p0013 :=
    @g_rexbii (syn_wbr (.cv u) (syn_c2nd) D) (.classEq D (syn_cfv (syn_c2nd) (.cv u))) u (syn_chwcn A) p0012
  have p0014 :=
    @g_bitri (.classMem D (syn_cima (syn_c2nd) (syn_chwcn A))) (syn_wrex u (syn_chwcn A) (syn_wbr (.cv u) (syn_c2nd) D)) (syn_wrex u (syn_chwcn A) (.classEq D (syn_cfv (syn_c2nd) (.cv u)))) p0002 p0013
  have p0015 :=
    @g_bitri (.classMem D (syn_chwbases A)) (.classMem D (syn_cima (syn_c2nd) (syn_chwcn A))) (syn_wrex u (syn_chwcn A) (.classEq D (syn_cfv (syn_c2nd) (.cv u)))) p0001 p0014
  exact p0015

noncomputable def g_hwcardsexg
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chwcards A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chwcards] using (Nominal.classEqRefl (syn_chwcards A)))
  have p0001 :=
    @g_enex
  have p0002 :=
    @g_a1i (.classMem (syn_cen) (syn_cvv)) (.classMem A (syn_cvv)) p0001
  have p0003 :=
    (by simpa [syn_chwbases] using (Nominal.classEqRefl (syn_chwbases A)))
  have p0004 :=
    @g_n_2ndex
  have p0005 :=
    @g_a1i (.classMem (syn_c2nd) (syn_cvv)) (.classMem A (syn_cvv)) p0004
  have p0006 :=
    @g_hwcnexg A
  have p0007 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_c2nd) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_imaexg (syn_c2nd) (syn_chwcn A) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_c2nd) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (.classMem (syn_cima (syn_c2nd) (syn_chwcn A)) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwbases A) (syn_cima (syn_c2nd) (syn_chwcn A)) (syn_cvv) p0003 p0009
  have p0011 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cen) (syn_cvv)) (.classMem (syn_chwbases A) (syn_cvv)) p0002 p0010
  have p0012 :=
    @g_qsexg (syn_chwbases A) (syn_cen) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_cen) (syn_cvv)) (.classMem (syn_chwbases A) (syn_cvv))) (.classMem (syn_cqs (syn_chwbases A) (syn_cen)) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwcards A) (syn_cqs (syn_chwbases A) (syn_cen)) (syn_cvv) p0000 p0013
  exact p0014

noncomputable def g_elhwcards
    (A : Class) (K : Class) (d : Var) (dv_A_K : Disjoint A.fv K.fv) (dv_A_d : d ∉ A.fv) (dv_K_d : d ∉ K.fv) (hyp_elhwcards_1 : Nominal.NPrf (.classMem K (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem K (syn_chwcards A)) (syn_wrex d (syn_chwbases A) (.classEq K (syn_cnc (.cv d))))) := by
  let proofSupport : Finset Var := A.fv ∪ K.fv ∪ ({d} : Finset Var)
  have dv_cache_0001 : d ∉ ((syn_chwbases A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : d ∉ (K).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_K_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((syn_cen)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chwcards] using (Nominal.classEqRefl (syn_chwcards A)))
  have p0001 :=
    @g_eleq2i (syn_chwcards A) (syn_cqs (syn_chwbases A) (syn_cen)) K p0000
  have p0002 :=
    @g_elqs d (syn_chwbases A) K (syn_cen) dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_elhwcards_1
  have p0003 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc (.cv d))))
  have p0004 :=
    @g_eqeq2i (syn_cnc (.cv d)) (syn_cec (.cv d) (syn_cen)) K p0003
  have p0005 :=
    @g_bicomi (.classEq K (syn_cnc (.cv d))) (.classEq K (syn_cec (.cv d) (syn_cen))) p0004
  have p0006 :=
    @g_rexbii (.classEq K (syn_cec (.cv d) (syn_cen))) (.classEq K (syn_cnc (.cv d))) d (syn_chwbases A) p0005
  have p0007 :=
    @g_bitri (.classMem K (syn_cqs (syn_chwbases A) (syn_cen))) (syn_wrex d (syn_chwbases A) (.classEq K (syn_cec (.cv d) (syn_cen)))) (syn_wrex d (syn_chwbases A) (.classEq K (syn_cnc (.cv d)))) p0002 p0006
  have p0008 :=
    @g_bitri (.classMem K (syn_chwcards A)) (.classMem K (syn_cqs (syn_chwbases A) (syn_cen))) (syn_wrex d (syn_chwbases A) (.classEq K (syn_cnc (.cv d)))) p0001 p0007
  exact p0008

noncomputable def g_hwcardssnc
    (A : Class) :
    Nominal.NPrf (syn_wss (syn_chwcards A) (syn_cncs)) := by
  let proofSupport : Finset Var := A.fv
  let k : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact fresh_k (h)
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (h)
  have fresh_k_ne_d : k ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_k : d ≠ k :=
    Ne.symm fresh_k_ne_d
  have dv_cache_0001 : Disjoint (A).fv ((Class.cv k)).fv := by
    exact (show Disjoint (A).fv ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({k} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show k ∉ (A).fv from (by exact fresh_k_not_A))))))
  have dv_cache_0002 : d ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ ((syn_chwcards A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : k ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex k
  have p0001 :=
    @g_elhwcards A (.cv k) d dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv k) (syn_chwcards A)) (syn_wrex d (syn_chwbases A) (.classEq (.cv k) (syn_cnc (.cv d)))) p0001
  have p0003 :=
    @g_rexex (.classEq (.cv k) (syn_cnc (.cv d))) d (syn_chwbases A)
  have p0004 :=
    @g_syl (.classMem (.cv k) (syn_chwcards A)) (syn_wrex d (syn_chwbases A) (.classEq (.cv k) (syn_cnc (.cv d)))) (syn_wex d (.classEq (.cv k) (syn_cnc (.cv d)))) p0002 p0003
  have p0005 :=
    @g_elncs d (.cv k) dv_cache_0003
  have p0006 :=
    @g_biimpri (.classMem (.cv k) (syn_cncs)) (syn_wex d (.classEq (.cv k) (syn_cnc (.cv d)))) p0005
  have p0007 :=
    @g_syl (.classMem (.cv k) (syn_chwcards A)) (syn_wex d (.classEq (.cv k) (syn_cnc (.cv d)))) (.classMem (.cv k) (syn_cncs)) p0004 p0006
  have p0008 :=
    @g_ssriv k (syn_chwcards A) (syn_cncs) dv_cache_0004 dv_cache_0005 p0007
  exact p0008

noncomputable def g_frrd
    (ph : Wff) (x : Var) (y : Var) (z : Var) (B : Class) (S : Class) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv) (dv_ph_x : x ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_frrd_1 : Nominal.NPrf (.imp ph (.classMem S (syn_cvv)))) (hyp_frrd_2 : Nominal.NPrf (.imp ph (.classMem B (syn_cvv)))) (hyp_frrd_3 : Nominal.NPrf (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.objEq y z)))))) :
    Nominal.NPrf (.imp ph (syn_wbr S (syn_cfound) B)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ B.fv ∪ S.fv
  let a : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_ph : a ∉ ph.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_ph : r ∉ ph.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_r_ne_z : r ≠ z := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_r : z ≠ r :=
    Ne.symm fresh_r_ne_z
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_a_ne_r : a ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_a : r ≠ a :=
    Ne.symm fresh_a_ne_r
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classEq (.cv r) S)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_r, dv_S_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv r) S)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv r) S)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv a) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0007 : a ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0008 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0009 : a ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0010 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0011 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : r ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0015 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0016 : r ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : r ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : r ∉ ((Wff.all x (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_B, fresh_r_ne_y, fresh_r_ne_z, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((Wff.all x (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_not_B, fresh_a_ne_y, fresh_a_ne_z, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000_e00_recanon : Nominal.NPrf (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
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
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      hyp_frrd_3
  have p0000 :=
    @g_ex ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))) p0000_e00_recanon
  have p0001 :=
    @g_alrimiv ph (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) x dv_cache_0001 p0000
  have p0002 :=
    @g_jca ph (.classMem S (syn_cvv)) (.classMem B (syn_cvv)) hyp_frrd_1 hyp_frrd_2
  have p0003 :=
    @g_breq (.cv y) (.cv z) (.cv r) S
  have p0004 :=
    @g_imbi1d (.classEq (.cv r) S) (syn_wbr (.cv y) (.cv r) (.cv z)) (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)) p0003
  have p0005 :=
    @g_rexralbidv (.classEq (.cv r) S) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z))) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))) z y (.cv x) (.cv x) dv_cache_0002 dv_cache_0003 p0004
  have p0006 :=
    @g_imbi2d (.classEq (.cv r) S) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z))))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))) (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) p0005
  have p0007 :=
    @g_albidv (.classEq (.cv r) S) (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z)))))) (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) x dv_cache_0004 p0006
  have p0008 :=
    @g_sseq2 (.cv a) B (.cv x)
  have p0009 :=
    @g_anbi1d (.classEq (.cv a) B) (syn_wss (.cv x) (.cv a)) (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)) p0008
  have p0010 :=
    @g_imbi1d (.classEq (.cv a) B) (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))) p0009
  have p0011 :=
    @g_albidv (.classEq (.cv a) B) (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) x dv_cache_0005 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_found x y z r a dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0013_e02_recanon : Nominal.NPrf (.classEq (syn_cfound) (syn_copab r a (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z))))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cfound syn_copab syn_wex syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wne syn_c0 syn_cdif syn_cvv syn_wrex syn_wral syn_wbr syn_cop syn_cun
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
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
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0012
  have p0013 :=
    @g_brabg (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z))))))) (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))) (.all x (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))) r a S B (syn_cvv) (syn_cvv) (syn_cfound) dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 p0007 p0011 p0013_e02_recanon
  have p0014 :=
    @g_syl ph (syn_wa (.classMem S (syn_cvv)) (.classMem B (syn_cvv))) (syn_wb (syn_wbr S (syn_cfound) B) (.all x (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))) p0002 p0013
  have p0015 :=
    @g_mpbird ph (syn_wbr S (syn_cfound) B) (.all x (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))) p0001 p0014
  exact p0015

#print axioms g_frrd

end NFChoice.DirectNominalPrf.WPPReplay
