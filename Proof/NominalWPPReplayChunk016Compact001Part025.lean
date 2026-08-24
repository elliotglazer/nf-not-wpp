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
import NominalWPPReplayChunk016Compact001Part024

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

noncomputable def g_siorndv
    (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) D) (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D))) := by
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
  have dv_cache_0001 : x ∉ ((syn_cpw1 D)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
    @g_brex R D (syn_cwe)
  have p0001 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0000
  have p0002 :=
    @g_siexg R (syn_cvv)
  have p0003 :=
    @g_syl (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem (syn_csi R) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_brex R D (syn_cwe)
  have p0005 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0004
  have p0006 :=
    @g_pw1exg D (syn_cvv)
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) D) (.classMem D (syn_cvv)) (.classMem (syn_cpw1 D) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
  have p0009 :=
    @g_wppweref D R
  have p0010 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cref) D) p0008 p0009
  have p0011 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
  have p0012 :=
    @g_hnwpw1argcl D x
  have p0013 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0011 p0012
  have p0014 :=
    @g_simpld (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0013
  have p0015 :=
    @g_refd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) D R (syn_cuni (.cv x)) p0010 p0014
  have p0016 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
  have p0017 :=
    @g_hnwpw1argcl D x
  have p0018 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0016 p0017
  have p0019 :=
    @g_simprd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0018
  have p0020 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))
  have p0021 :=
    @g_hnwpw1argcl D x
  have p0022 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0020 p0021
  have p0023 :=
    @g_simprd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0022
  have p0024 :=
    @g_breq12d (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (.cv x) (syn_csn (syn_cuni (.cv x))) (.cv x) (syn_csn (syn_cuni (.cv x))) (syn_csi R) p0019 p0023
  have p0025 :=
    @g_vex x
  have p0026 :=
    @g_uniex (.cv x) p0025
  have p0027 :=
    @g_vex x
  have p0028 :=
    @g_uniex (.cv x) p0027
  have p0029 :=
    @g_brsnsi (syn_cuni (.cv x)) (syn_cuni (.cv x)) R p0026 p0028
  have p0030 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv x)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv x)))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) p0029
  have p0031 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (syn_wbr (.cv x) (syn_csi R) (.cv x)) (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv x)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv x))) p0024 p0030
  have p0032 :=
    @g_biimprd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (syn_wbr (.cv x) (syn_csi R) (.cv x)) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv x))) p0031
  have p0033 :=
    @g_mpd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv x))) (syn_wbr (.cv x) (syn_csi R) (.cv x)) p0015 p0032
  have p0034 :=
    @g_simp1 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0035 :=
    @g_wppwepo D R
  have p0036 :=
    @g_porta D R
  have p0037 :=
    @g_simp2bi (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0036
  have p0038 :=
    @g_syl (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_ctrans) D) p0035 p0037
  have p0039 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_ctrans) D) p0034 p0038
  have p0040 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0041 :=
    @g_simp1 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))
  have p0042 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) p0040 p0041
  have p0043 :=
    @g_hnwpw1argcl D x
  have p0044 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0042 p0043
  have p0045 :=
    @g_simpld (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0044
  have p0046 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0047 :=
    @g_simp2 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))
  have p0048 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) p0046 p0047
  have p0049 :=
    @g_hnwpw1argcl D y
  have p0050 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0048 p0049
  have p0051 :=
    @g_simpld (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0050
  have p0052 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0053 :=
    @g_simp3 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))
  have p0054 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 D)) p0052 p0053
  have p0055 :=
    @g_hnwpw1argcl D z
  have p0056 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (.cv z) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv z)) D) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z))))) p0054 p0055
  have p0057 :=
    @g_simpld (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (syn_cuni (.cv z)) D) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0056
  have p0058 :=
    @g_simp3 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0059 :=
    @g_simpl (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z))
  have p0060 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) p0058 p0059
  have p0061 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0062 :=
    @g_simp1 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))
  have p0063 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) p0061 p0062
  have p0064 :=
    @g_hnwpw1argcl D x
  have p0065 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0063 p0064
  have p0066 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0065
  have p0067 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0068 :=
    @g_simp2 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))
  have p0069 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) p0067 p0068
  have p0070 :=
    @g_hnwpw1argcl D y
  have p0071 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0069 p0070
  have p0072 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0071
  have p0073 :=
    @g_breq12d (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.cv x) (syn_csn (syn_cuni (.cv x))) (.cv y) (syn_csn (syn_cuni (.cv y))) (syn_csi R) p0066 p0072
  have p0074 :=
    @g_vex x
  have p0075 :=
    @g_uniex (.cv x) p0074
  have p0076 :=
    @g_vex y
  have p0077 :=
    @g_uniex (.cv y) p0076
  have p0078 :=
    @g_brsnsi (syn_cuni (.cv x)) (syn_cuni (.cv y)) R p0075 p0077
  have p0079 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y)))) (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) p0078
  have p0080 :=
    @g_bitrd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0073 p0079
  have p0081 :=
    @g_biimpd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0080
  have p0082 :=
    @g_mpd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0060 p0081
  have p0083 :=
    @g_simp3 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0084 :=
    @g_simpr (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z))
  have p0085 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z))) (syn_wbr (.cv y) (syn_csi R) (.cv z)) p0083 p0084
  have p0086 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0087 :=
    @g_simp2 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))
  have p0088 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) p0086 p0087
  have p0089 :=
    @g_hnwpw1argcl D y
  have p0090 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0088 p0089
  have p0091 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0090
  have p0092 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0093 :=
    @g_simp3 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))
  have p0094 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 D)) p0092 p0093
  have p0095 :=
    @g_hnwpw1argcl D z
  have p0096 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (.cv z) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv z)) D) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z))))) p0094 p0095
  have p0097 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (syn_cuni (.cv z)) D) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0096
  have p0098 :=
    @g_breq12d (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.cv y) (syn_csn (syn_cuni (.cv y))) (.cv z) (syn_csn (syn_cuni (.cv z))) (syn_csi R) p0091 p0097
  have p0099 :=
    @g_vex y
  have p0100 :=
    @g_uniex (.cv y) p0099
  have p0101 :=
    @g_vex z
  have p0102 :=
    @g_uniex (.cv z) p0101
  have p0103 :=
    @g_brsnsi (syn_cuni (.cv y)) (syn_cuni (.cv z)) R p0100 p0102
  have p0104 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv z)))) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv z)))) (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) p0103
  have p0105 :=
    @g_bitrd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr (.cv y) (syn_csi R) (.cv z)) (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv z)))) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv z))) p0098 p0104
  have p0106 :=
    @g_biimpd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr (.cv y) (syn_csi R) (.cv z)) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv z))) p0105
  have p0107 :=
    @g_mpd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr (.cv y) (syn_csi R) (.cv z)) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv z))) p0085 p0106
  have p0108 :=
    @g_trd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) D R (syn_cuni (.cv x)) (syn_cuni (.cv y)) (syn_cuni (.cv z)) p0039 p0045 p0051 p0057 p0082 p0107
  have p0109 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0110 :=
    @g_simp1 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))
  have p0111 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) p0109 p0110
  have p0112 :=
    @g_hnwpw1argcl D x
  have p0113 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0111 p0112
  have p0114 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0113
  have p0115 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))
  have p0116 :=
    @g_simp3 (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))
  have p0117 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 D)) p0115 p0116
  have p0118 :=
    @g_hnwpw1argcl D z
  have p0119 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (.cv z) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv z)) D) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z))))) p0117 p0118
  have p0120 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.classMem (syn_cuni (.cv z)) D) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0119
  have p0121 :=
    @g_breq12d (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (.cv x) (syn_csn (syn_cuni (.cv x))) (.cv z) (syn_csn (syn_cuni (.cv z))) (syn_csi R) p0114 p0120
  have p0122 :=
    @g_vex x
  have p0123 :=
    @g_uniex (.cv x) p0122
  have p0124 :=
    @g_vex z
  have p0125 :=
    @g_uniex (.cv z) p0124
  have p0126 :=
    @g_brsnsi (syn_cuni (.cv x)) (syn_cuni (.cv z)) R p0123 p0125
  have p0127 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv z)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv z)))) (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) p0126
  have p0128 :=
    @g_bitrd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr (.cv x) (syn_csi R) (.cv z)) (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv z)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv z))) p0121 p0127
  have p0129 :=
    @g_biimprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr (.cv x) (syn_csi R) (.cv z)) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv z))) p0128
  have p0130 :=
    @g_mpd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_w3a (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (.cv z) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv z)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv z))) (syn_wbr (.cv x) (syn_csi R) (.cv z)) p0108 p0129
  have p0131 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0132 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0133 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) p0131 p0132
  have p0134 :=
    @g_hnwpw1argcl D x
  have p0135 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0133 p0134
  have p0136 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0135
  have p0137 :=
    @g_simp1 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0138 :=
    @g_wppweantisym D R
  have p0139 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cantisym) D) p0137 p0138
  have p0140 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0141 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0142 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) p0140 p0141
  have p0143 :=
    @g_hnwpw1argcl D x
  have p0144 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0142 p0143
  have p0145 :=
    @g_simpld (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0144
  have p0146 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0147 :=
    @g_simpr (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0148 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) p0146 p0147
  have p0149 :=
    @g_hnwpw1argcl D y
  have p0150 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0148 p0149
  have p0151 :=
    @g_simpld (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0150
  have p0152 :=
    @g_simp3 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0153 :=
    @g_simpl (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))
  have p0154 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) p0152 p0153
  have p0155 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0156 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0157 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) p0155 p0156
  have p0158 :=
    @g_hnwpw1argcl D x
  have p0159 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0157 p0158
  have p0160 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0159
  have p0161 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0162 :=
    @g_simpr (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0163 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) p0161 p0162
  have p0164 :=
    @g_hnwpw1argcl D y
  have p0165 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0163 p0164
  have p0166 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0165
  have p0167 :=
    @g_breq12d (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.cv x) (syn_csn (syn_cuni (.cv x))) (.cv y) (syn_csn (syn_cuni (.cv y))) (syn_csi R) p0160 p0166
  have p0168 :=
    @g_vex x
  have p0169 :=
    @g_uniex (.cv x) p0168
  have p0170 :=
    @g_vex y
  have p0171 :=
    @g_uniex (.cv y) p0170
  have p0172 :=
    @g_brsnsi (syn_cuni (.cv x)) (syn_cuni (.cv y)) R p0169 p0171
  have p0173 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y)))) (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) p0172
  have p0174 :=
    @g_bitrd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0167 p0173
  have p0175 :=
    @g_biimpd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0174
  have p0176 :=
    @g_mpd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0154 p0175
  have p0177 :=
    @g_simp3 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0178 :=
    @g_simpr (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))
  have p0179 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))) (syn_wbr (.cv y) (syn_csi R) (.cv x)) p0177 p0178
  have p0180 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0181 :=
    @g_simpr (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0182 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) p0180 p0181
  have p0183 :=
    @g_hnwpw1argcl D y
  have p0184 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0182 p0183
  have p0185 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0184
  have p0186 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0187 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0188 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) p0186 p0187
  have p0189 :=
    @g_hnwpw1argcl D x
  have p0190 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0188 p0189
  have p0191 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0190
  have p0192 :=
    @g_breq12d (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.cv y) (syn_csn (syn_cuni (.cv y))) (.cv x) (syn_csn (syn_cuni (.cv x))) (syn_csi R) p0185 p0191
  have p0193 :=
    @g_vex y
  have p0194 :=
    @g_uniex (.cv y) p0193
  have p0195 :=
    @g_vex x
  have p0196 :=
    @g_uniex (.cv x) p0195
  have p0197 :=
    @g_brsnsi (syn_cuni (.cv y)) (syn_cuni (.cv x)) R p0194 p0196
  have p0198 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv x)))) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x)))) (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) p0197
  have p0199 :=
    @g_bitrd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wbr (.cv y) (syn_csi R) (.cv x)) (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv x)))) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0192 p0198
  have p0200 :=
    @g_biimpd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wbr (.cv y) (syn_csi R) (.cv x)) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0199
  have p0201 :=
    @g_mpd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wbr (.cv y) (syn_csi R) (.cv x)) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0179 p0200
  have p0202 :=
    @g_antid (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) D R (syn_cuni (.cv x)) (syn_cuni (.cv y)) p0139 p0145 p0151 p0176 p0201
  have p0203 :=
    @g_sneqd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_cuni (.cv x)) (syn_cuni (.cv y)) p0202
  have p0204 :=
    @g_eqtrd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.cv x) (syn_csn (syn_cuni (.cv x))) (syn_csn (syn_cuni (.cv y))) p0136 p0203
  have p0205 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))
  have p0206 :=
    @g_simpr (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0207 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) p0205 p0206
  have p0208 :=
    @g_hnwpw1argcl D y
  have p0209 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0207 p0208
  have p0210 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0209
  have p0211 :=
    @g_eqcomd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.cv y) (syn_csn (syn_cuni (.cv y))) p0210
  have p0212 :=
    @g_eqtrd (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.cv x) (syn_csn (syn_cuni (.cv y))) (.cv y) p0204 p0211
  have p0213 :=
    @g_simp1 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0214 :=
    @g_wppweconnex D R
  have p0215 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cconnex) D) p0213 p0214
  have p0216 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0217 :=
    @g_hnwpw1argcl D x
  have p0218 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0216 p0217
  have p0219 :=
    @g_simpld (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0218
  have p0220 :=
    @g_simp3 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0221 :=
    @g_hnwpw1argcl D y
  have p0222 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0220 p0221
  have p0223 :=
    @g_simpld (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0222
  have p0224 :=
    @g_connexd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) D R (syn_cuni (.cv x)) (syn_cuni (.cv y)) p0215 p0219 p0223
  have p0225 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0226 :=
    @g_hnwpw1argcl D x
  have p0227 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0225 p0226
  have p0228 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0227
  have p0229 :=
    @g_simp3 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0230 :=
    @g_hnwpw1argcl D y
  have p0231 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0229 p0230
  have p0232 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0231
  have p0233 :=
    @g_breq12d (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.cv x) (syn_csn (syn_cuni (.cv x))) (.cv y) (syn_csn (syn_cuni (.cv y))) (syn_csi R) p0228 p0232
  have p0234 :=
    @g_vex x
  have p0235 :=
    @g_uniex (.cv x) p0234
  have p0236 :=
    @g_vex y
  have p0237 :=
    @g_uniex (.cv y) p0236
  have p0238 :=
    @g_brsnsi (syn_cuni (.cv x)) (syn_cuni (.cv y)) R p0235 p0237
  have p0239 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y)))) (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) p0238
  have p0240 :=
    @g_bitrd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (syn_csn (syn_cuni (.cv x))) (syn_csi R) (syn_csn (syn_cuni (.cv y)))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0233 p0239
  have p0241 :=
    @g_biimprd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) p0240
  have p0242 :=
    @g_orc (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))
  have p0243 :=
    @g_syl6 (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wo (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))) p0241 p0242
  have p0244 :=
    @g_simp3 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0245 :=
    @g_hnwpw1argcl D y
  have p0246 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv y) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y))))) p0244 p0245
  have p0247 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (syn_cuni (.cv y)) D) (.classEq (.cv y) (syn_csn (syn_cuni (.cv y)))) p0246
  have p0248 :=
    @g_simp2 (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))
  have p0249 :=
    @g_hnwpw1argcl D x
  have p0250 :=
    @g_syl (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (.cv x) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x))))) p0248 p0249
  have p0251 :=
    @g_simprd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (syn_cuni (.cv x)) D) (.classEq (.cv x) (syn_csn (syn_cuni (.cv x)))) p0250
  have p0252 :=
    @g_breq12d (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.cv y) (syn_csn (syn_cuni (.cv y))) (.cv x) (syn_csn (syn_cuni (.cv x))) (syn_csi R) p0247 p0251
  have p0253 :=
    @g_vex y
  have p0254 :=
    @g_uniex (.cv y) p0253
  have p0255 :=
    @g_vex x
  have p0256 :=
    @g_uniex (.cv x) p0255
  have p0257 :=
    @g_brsnsi (syn_cuni (.cv y)) (syn_cuni (.cv x)) R p0254 p0256
  have p0258 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv x)))) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x)))) (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) p0257
  have p0259 :=
    @g_bitrd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wbr (.cv y) (syn_csi R) (.cv x)) (syn_wbr (syn_csn (syn_cuni (.cv y))) (syn_csi R) (syn_csn (syn_cuni (.cv x)))) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0252 p0258
  have p0260 :=
    @g_biimprd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wbr (.cv y) (syn_csi R) (.cv x)) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0259
  have p0261 :=
    @g_olc (syn_wbr (.cv y) (syn_csi R) (.cv x)) (syn_wbr (.cv x) (syn_csi R) (.cv y))
  have p0262 :=
    @g_syl6 (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) (syn_wbr (.cv y) (syn_csi R) (.cv x)) (syn_wo (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))) p0260 p0261
  have p0263 :=
    @g_jaod (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) (syn_wo (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x))) p0243 p0262
  have p0264 :=
    @g_mpd (syn_w3a (syn_wbr R (syn_cwe) D) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wo (syn_wbr (syn_cuni (.cv x)) R (syn_cuni (.cv y))) (syn_wbr (syn_cuni (.cv y)) R (syn_cuni (.cv x)))) (syn_wo (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x))) p0224 p0263
  have p0265_e04_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (syn_wa (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wbr (.cv y) (syn_csi R) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi syn_cwe syn_cin syn_cstrict syn_cfound syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0212
  have p0265 :=
    @g_sod (syn_wbr R (syn_cwe) D) x y z (syn_cpw1 D) (syn_csi R) (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0003 p0007 p0033 p0130 p0265_e04_recanon p0264
  exact p0265

#print axioms g_siorndv

end NFChoice.DirectNominalPrf.WPPReplay
