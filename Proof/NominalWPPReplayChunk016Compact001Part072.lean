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
import NominalWPPReplayChunk016Compact001Part071

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

noncomputable def g_siorreflectndv
    (D : Class) (R : Class) (hyp_siorreflectndv_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_siorreflectndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cstrict) D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_a1i (.classMem R (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_siorreflectndv_1
  have p0001 :=
    @g_a1i (.classMem D (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_siorreflectndv_2
  have p0002 :=
    @g_simpl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
  have p0003 :=
    @g_wppweref (syn_cpw1 D) (syn_csi R)
  have p0004 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cref) (syn_cpw1 D)) p0002 p0003
  have p0005 :=
    @g_simpr (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
  have p0006 :=
    @g_snelpw1 (.cv x) D
  have p0007 :=
    @g_biimpri (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0006
  have p0008 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)) (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0005 p0007
  have p0009 :=
    @g_refd (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)) (syn_cpw1 D) (syn_csi R) (syn_csn (.cv x)) p0004 p0008
  have p0010 :=
    @g_vex x
  have p0011 :=
    @g_vex x
  have p0012 :=
    @g_brsnsi (.cv x) (.cv x) R p0010 p0011
  have p0013 :=
    @g_biimpi (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv x))) (syn_wbr (.cv x) R (.cv x)) p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)) (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv x))) (syn_wbr (.cv x) R (.cv x)) p0009 p0013
  have p0015 :=
    @g_refrd (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x D R (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000 p0001 p0014
  have p0016 :=
    @g_a1i (.classMem R (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_siorreflectndv_1
  have p0017 :=
    @g_a1i (.classMem D (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_siorreflectndv_2
  have p0018 :=
    @g_simp1 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
  have p0019 :=
    @g_wppwepo (syn_cpw1 D) (syn_csi R)
  have p0020 :=
    @g_porta (syn_cpw1 D) (syn_csi R)
  have p0021 :=
    @g_simp2bi (syn_wbr (syn_csi R) (syn_cpartial) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cref) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_ctrans) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cantisym) (syn_cpw1 D)) p0020
  have p0022 :=
    @g_syl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cpartial) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_ctrans) (syn_cpw1 D)) p0019 p0021
  have p0023 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_ctrans) (syn_cpw1 D)) p0018 p0022
  have p0024 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
  have p0025 :=
    @g_simp1 (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)
  have p0026 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (.classMem (.cv x) D) p0024 p0025
  have p0027 :=
    @g_snelpw1 (.cv x) D
  have p0028 :=
    @g_biimpri (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0027
  have p0029 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0026 p0028
  have p0030 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
  have p0031 :=
    @g_simp2 (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)
  have p0032 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (.classMem (.cv y) D) p0030 p0031
  have p0033 :=
    @g_snelpw1 (.cv y) D
  have p0034 :=
    @g_biimpri (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) (.classMem (.cv y) D) p0033
  have p0035 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv y) D) (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) p0032 p0034
  have p0036 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
  have p0037 :=
    @g_simp3 (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)
  have p0038 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (.classMem (.cv z) D) p0036 p0037
  have p0039 :=
    @g_snelpw1 (.cv z) D
  have p0040 :=
    @g_biimpri (.classMem (syn_csn (.cv z)) (syn_cpw1 D)) (.classMem (.cv z) D) p0039
  have p0041 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv z) D) (.classMem (syn_csn (.cv z)) (syn_cpw1 D)) p0038 p0040
  have p0042 :=
    @g_simp3 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
  have p0043 :=
    @g_simpl (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))
  have p0044 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))) (syn_wbr (.cv x) R (.cv y)) p0042 p0043
  have p0045 :=
    @g_vex x
  have p0046 :=
    @g_vex y
  have p0047 :=
    @g_brsnsi (.cv x) (.cv y) R p0045 p0046
  have p0048 :=
    @g_biimpri (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)) p0047
  have p0049 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) p0044 p0048
  have p0050 :=
    @g_simp3 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
  have p0051 :=
    @g_simpr (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))
  have p0052 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))) (syn_wbr (.cv y) R (.cv z)) p0050 p0051
  have p0053 :=
    @g_vex y
  have p0054 :=
    @g_vex z
  have p0055 :=
    @g_brsnsi (.cv y) (.cv z) R p0053 p0054
  have p0056 :=
    @g_biimpri (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv z))) (syn_wbr (.cv y) R (.cv z)) p0055
  have p0057 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wbr (.cv y) R (.cv z)) (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv z))) p0052 p0056
  have p0058 :=
    @g_trd (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_cpw1 D) (syn_csi R) (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_csn (.cv z)) p0023 p0029 p0035 p0041 p0049 p0057
  have p0059 :=
    @g_vex x
  have p0060 :=
    @g_vex z
  have p0061 :=
    @g_brsnsi (.cv x) (.cv z) R p0059 p0060
  have p0062 :=
    @g_biimpi (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv z))) (syn_wbr (.cv x) R (.cv z)) p0061
  have p0063 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv z))) (syn_wbr (.cv x) R (.cv z)) p0058 p0062
  have p0064 :=
    @g_trrd (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x y z D R (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0016 p0017 p0063
  have p0065 :=
    @g_a1i (.classMem R (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_siorreflectndv_1
  have p0066 :=
    @g_a1i (.classMem D (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_siorreflectndv_2
  have p0067 :=
    @g_simp1 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0068 :=
    @g_wppweantisym (syn_cpw1 D) (syn_csi R)
  have p0069 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cantisym) (syn_cpw1 D)) p0067 p0068
  have p0070 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0071 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0072 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0070 p0071
  have p0073 :=
    @g_snelpw1 (.cv x) D
  have p0074 :=
    @g_biimpri (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0073
  have p0075 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0072 p0074
  have p0076 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0077 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0078 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0076 p0077
  have p0079 :=
    @g_snelpw1 (.cv y) D
  have p0080 :=
    @g_biimpri (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) (.classMem (.cv y) D) p0079
  have p0081 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.classMem (.cv y) D) (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) p0078 p0080
  have p0082 :=
    @g_simp3 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0083 :=
    @g_simpl (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))
  have p0084 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv x) R (.cv y)) p0082 p0083
  have p0085 :=
    @g_vex x
  have p0086 :=
    @g_vex y
  have p0087 :=
    @g_brsnsi (.cv x) (.cv y) R p0085 p0086
  have p0088 :=
    @g_biimpri (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)) p0087
  have p0089 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) p0084 p0088
  have p0090 :=
    @g_simp3 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0091 :=
    @g_simpr (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))
  have p0092 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv y) R (.cv x)) p0090 p0091
  have p0093 :=
    @g_vex y
  have p0094 :=
    @g_vex x
  have p0095 :=
    @g_brsnsi (.cv y) (.cv x) R p0093 p0094
  have p0096 :=
    @g_biimpri (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x))) (syn_wbr (.cv y) R (.cv x)) p0095
  have p0097 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_wbr (.cv y) R (.cv x)) (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x))) p0092 p0096
  have p0098 :=
    @g_antid (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_cpw1 D) (syn_csi R) (syn_csn (.cv x)) (syn_csn (.cv y)) p0069 p0075 p0081 p0089 p0097
  have p0099 :=
    @g_vex x
  have p0100 :=
    @g_sneqr (.cv x) (.cv y) p0099
  have p0101 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.classEq (syn_csn (.cv x)) (syn_csn (.cv y))) (.classEq (.cv x) (.cv y)) p0098 p0100
  have p0102_e02_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi syn_csi syn_copab syn_cwe syn_cin syn_cstrict syn_cfound syn_cpw1
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0101
  have p0102 :=
    @g_antird (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x y D R (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0006 dv_cache_0003 dv_cache_0008 dv_cache_0010 p0065 p0066 p0102_e02_recanon
  have p0103 :=
    @g_n_3jca (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0015 p0064 p0102
  have p0104 :=
    @g_porta D R
  have p0105 :=
    @g_biimpri (syn_wbr R (syn_cpartial) D) (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D)) p0104
  have p0106 :=
    @g_syl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D)) (syn_wbr R (syn_cpartial) D) p0103 p0105
  have p0107 :=
    @g_a1i (.classMem R (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_siorreflectndv_1
  have p0108 :=
    @g_a1i (.classMem D (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_siorreflectndv_2
  have p0109 :=
    @g_simp1 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0110 :=
    @g_wppweconnex (syn_cpw1 D) (syn_csi R)
  have p0111 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cconnex) (syn_cpw1 D)) p0109 p0110
  have p0112 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0113 :=
    @g_snelpw1 (.cv x) D
  have p0114 :=
    @g_biimpri (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0113
  have p0115 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0112 p0114
  have p0116 :=
    @g_simp3 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0117 :=
    @g_snelpw1 (.cv y) D
  have p0118 :=
    @g_biimpri (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) (.classMem (.cv y) D) p0117
  have p0119 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) p0116 p0118
  have p0120 :=
    @g_connexd (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_cpw1 D) (syn_csi R) (syn_csn (.cv x)) (syn_csn (.cv y)) p0111 p0115 p0119
  have p0121 :=
    @g_vex x
  have p0122 :=
    @g_vex y
  have p0123 :=
    @g_brsnsi (.cv x) (.cv y) R p0121 p0122
  have p0124 :=
    @g_vex y
  have p0125 :=
    @g_vex x
  have p0126 :=
    @g_brsnsi (.cv y) (.cv x) R p0124 p0125
  have p0127 :=
    @g_orbi12i (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x))) (syn_wbr (.cv y) R (.cv x)) p0123 p0126
  have p0128 :=
    @g_biimpi (syn_wo (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x)))) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) p0127
  have p0129 :=
    @g_syl (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wo (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x)))) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) p0120 p0128
  have p0130 :=
    @g_connexrd (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x y D R (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0006 dv_cache_0003 dv_cache_0008 dv_cache_0010 p0107 p0108 p0129
  have p0131 :=
    @g_jca (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0106 p0130
  have p0132 :=
    @g_sopc D R
  have p0133 :=
    @g_biimpri (syn_wbr R (syn_cstrict) D) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0132
  have p0134 :=
    @g_syl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) (syn_wbr R (syn_cstrict) D) p0131 p0133
  exact p0134

#print axioms g_siorreflectndv

end NFChoice.DirectNominalPrf.WPPReplay
