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
import NominalWPPReplayChunk016Compact001Part066

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

noncomputable def g_pw1typedbrcldv
    (D : Class) (P : Class) (Q : Class) (R : Class) (hyp_pw1typedbrcldv_1 : Nominal.NPrf (.classMem P (syn_cvv))) (hyp_pw1typedbrcldv_2 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) (syn_wb (syn_wbr P (syn_csi R) Q) (syn_wbr (syn_cuni P) R (syn_cuni Q)))) := by
  let proofSupport : Finset Var := D.fv ∪ P.fv ∪ Q.fv ∪ R.fv
  have p0000 :=
    @g_simpl (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))
  have p0001 :=
    @g_pw1argclcl D P
  have p0002 :=
    @g_syl (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) (.classMem P (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni P) D) (.classEq P (syn_csn (syn_cuni P)))) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (syn_cuni P) D) (.classEq P (syn_csn (syn_cuni P)))
  have p0004 :=
    @g_syl (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni P) D) (.classEq P (syn_csn (syn_cuni P)))) (.classEq P (syn_csn (syn_cuni P))) p0002 p0003
  have p0005 :=
    @g_simpr (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))
  have p0006 :=
    @g_pw1argclcl D Q
  have p0007 :=
    @g_syl (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) (.classMem Q (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q)))) p0005 p0006
  have p0008 :=
    @g_simpr (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0009 :=
    @g_syl (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q)))) (.classEq Q (syn_csn (syn_cuni Q))) p0007 p0008
  have p0010 :=
    @g_breq12d (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) P (syn_csn (syn_cuni P)) Q (syn_csn (syn_cuni Q)) (syn_csi R) p0004 p0009
  have p0011 :=
    @g_uniex P hyp_pw1typedbrcldv_1
  have p0012 :=
    @g_uniex Q hyp_pw1typedbrcldv_2
  have p0013 :=
    @g_brsnsi (syn_cuni P) (syn_cuni Q) R p0011 p0012
  have p0014 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni P)) (syn_csi R) (syn_csn (syn_cuni Q))) (syn_wbr (syn_cuni P) R (syn_cuni Q))) (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) p0013
  have p0015 :=
    @g_bitrd (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) (syn_wbr P (syn_csi R) Q) (syn_wbr (syn_csn (syn_cuni P)) (syn_csi R) (syn_csn (syn_cuni Q))) (syn_wbr (syn_cuni P) R (syn_cuni Q)) p0010 p0014
  exact p0015

noncomputable def g_pw1descentisomdv
    (z : Var) (D : Class) (R : Class) (S : Class) (g : Var) (E : Class) (dv_D_z : z ∉ D.fv) (dv_E_z : z ∉ E.fv) (dv_g_z : g ≠ z) :
    Nominal.NPrf (.imp (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E)) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({g} : Finset Var) ∪ E.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_ne_g : a ≠ g := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_a : g ≠ a :=
    Ne.symm fresh_a_ne_g
  have fresh_a_not_E : a ∉ E.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_z : b ≠ z := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_b : z ≠ b :=
    Ne.symm fresh_b_ne_z
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_g : b ≠ g := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_b : g ≠ b :=
    Ne.symm fresh_b_ne_g
  have fresh_b_not_E : b ∉ E.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : z ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (E).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show g ≠ z from (by exact dv_g_z))
  have dv_cache_0004 : z ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, (Ne.symm dv_g_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_b, (Ne.symm dv_g_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_D, fresh_a_not_E, fresh_a_ne_g, fresh_a_not_R, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : b ∉ ((syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_D, fresh_b_not_E, fresh_b_ne_g, fresh_b_not_R, fresh_b_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0012 : a ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : b ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_D, fresh_a_ne_z, fresh_a_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ ((syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_D, fresh_b_ne_z, fresh_b_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : b ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_isof1o (syn_cpw1 D) (syn_cpw1 E) (syn_csi R) (syn_csi S) (.cv g)
  have p0001 :=
    @g_pw1descentf1odv z D g E dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E) p0000 p0001
  have p0003 :=
    @g_vex a
  have p0004 :=
    @g_vex b
  have p0005 :=
    @g_brsnsi (.cv a) (.cv b) R p0003 p0004
  have p0006 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (.cv a)) (syn_csi R) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))) (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) p0005
  have p0007 :=
    @g_bicomd (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wbr (syn_csn (.cv a)) (syn_csi R) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b)) p0006
  have p0008 :=
    @g_simpl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0009 :=
    @g_simpr (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0010 :=
    @g_simpl (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0011 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv a) D) p0009 p0010
  have p0012 :=
    @g_snelpw1 (.cv a) D
  have p0013 :=
    @g_sylibr (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (.classMem (.cv a) D) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0011 p0012
  have p0014 :=
    @g_simpr (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0015 :=
    @g_simpr (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0016 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv b) D) p0014 p0015
  have p0017 :=
    @g_snelpw1 (.cv b) D
  have p0018 :=
    @g_sylibr (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (.classMem (.cv b) D) (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) p0016 p0017
  have p0019 :=
    @g_jca (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) p0013 p0018
  have p0020 :=
    @g_jca (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))) p0008 p0019
  have p0021 :=
    @g_isorel (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_csi R) (syn_csi S) (.cv g)
  have p0022 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D)))) (syn_wb (syn_wbr (syn_csn (.cv a)) (syn_csi R) (syn_csn (.cv b))) (syn_wbr (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csi S) (syn_cfv (.cv g) (syn_csn (.cv b))))) p0020 p0021
  have p0023 :=
    @g_bitrd (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wbr (.cv a) R (.cv b)) (syn_wbr (syn_csn (.cv a)) (syn_csi R) (syn_csn (.cv b))) (syn_wbr (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csi S) (syn_cfv (.cv g) (syn_csn (.cv b)))) p0007 p0022
  have p0024 :=
    @g_simpl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0025 :=
    @g_isof1o (syn_cpw1 D) (syn_cpw1 E) (syn_csi R) (syn_csi S) (.cv g)
  have p0026 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0024 p0025
  have p0027 :=
    @g_f1of (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0028 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0026 p0027
  have p0029 :=
    @g_simpr (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0030 :=
    @g_simpl (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0031 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv a) D) p0029 p0030
  have p0032 :=
    @g_snelpw1 (.cv a) D
  have p0033 :=
    @g_sylibr (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (.classMem (.cv a) D) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0031 p0032
  have p0034 :=
    @g_jca (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0028 p0033
  have p0035 :=
    @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv a)) (.cv g)
  have p0036 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D))) (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E)) p0034 p0035
  have p0037 :=
    @g_simpl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0038 :=
    @g_isof1o (syn_cpw1 D) (syn_cpw1 E) (syn_csi R) (syn_csi S) (.cv g)
  have p0039 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0037 p0038
  have p0040 :=
    @g_f1of (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0041 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0039 p0040
  have p0042 :=
    @g_simpr (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0043 :=
    @g_simpr (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0044 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv b) D) p0042 p0043
  have p0045 :=
    @g_snelpw1 (.cv b) D
  have p0046 :=
    @g_sylibr (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (.classMem (.cv b) D) (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) p0044 p0045
  have p0047 :=
    @g_jca (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) p0041 p0046
  have p0048 :=
    @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv b)) (.cv g)
  have p0049 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))) (.classMem (syn_cfv (.cv g) (syn_csn (.cv b))) (syn_cpw1 E)) p0047 p0048
  have p0050 :=
    @g_jca (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E)) (.classMem (syn_cfv (.cv g) (syn_csn (.cv b))) (syn_cpw1 E)) p0036 p0049
  have p0051 :=
    @g_fvex (syn_csn (.cv a)) (.cv g)
  have p0052 :=
    @g_fvex (syn_csn (.cv b)) (.cv g)
  have p0053 :=
    @g_pw1typedbrcldv E (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cfv (.cv g) (syn_csn (.cv b))) S p0051 p0052
  have p0054 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E)) (.classMem (syn_cfv (.cv g) (syn_csn (.cv b))) (syn_cpw1 E))) (syn_wb (syn_wbr (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csi S) (syn_cfv (.cv g) (syn_csn (.cv b)))) (syn_wbr (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) S (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b)))))) p0050 p0053
  have p0055 :=
    @g_bitrd (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wbr (.cv a) R (.cv b)) (syn_wbr (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csi S) (syn_cfv (.cv g) (syn_csn (.cv b)))) (syn_wbr (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) S (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b))))) p0023 p0054
  have p0056 :=
    @g_simpr (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0057 :=
    @g_simpl (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0058 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv a) D) p0056 p0057
  have p0059 :=
    @g_id (.classEq (.cv z) (.cv a))
  have p0060 :=
    @g_sneqd (.classEq (.cv z) (.cv a)) (.cv z) (.cv a) p0059
  have p0061 :=
    @g_fveq2d (.classEq (.cv z) (.cv a)) (syn_csn (.cv z)) (syn_csn (.cv a)) (.cv g) p0060
  have p0062 :=
    @g_unieqd (.classEq (.cv z) (.cv a)) (syn_cfv (.cv g) (syn_csn (.cv z))) (syn_cfv (.cv g) (syn_csn (.cv a))) p0061
  have p0063 :=
    @g_eqid (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0064 :=
    @g_fvex (syn_csn (.cv a)) (.cv g)
  have p0065 :=
    @g_uniex (syn_cfv (.cv g) (syn_csn (.cv a))) p0064
  have p0066 :=
    @g_fvmpt z (.cv a) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) D (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0004 dv_cache_0005 dv_cache_0001 p0062 p0063 p0065
  have p0067 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (.classMem (.cv a) D) (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) p0058 p0066
  have p0068 :=
    @g_eqcomd (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) p0067
  have p0069 :=
    @g_simpr (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0070 :=
    @g_simpr (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0071 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv b) D) p0069 p0070
  have p0072 :=
    @g_id (.classEq (.cv z) (.cv b))
  have p0073 :=
    @g_sneqd (.classEq (.cv z) (.cv b)) (.cv z) (.cv b) p0072
  have p0074 :=
    @g_fveq2d (.classEq (.cv z) (.cv b)) (syn_csn (.cv z)) (syn_csn (.cv b)) (.cv g) p0073
  have p0075 :=
    @g_unieqd (.classEq (.cv z) (.cv b)) (syn_cfv (.cv g) (syn_csn (.cv z))) (syn_cfv (.cv g) (syn_csn (.cv b))) p0074
  have p0076 :=
    @g_eqid (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0077 :=
    @g_fvex (syn_csn (.cv b)) (.cv g)
  have p0078 :=
    @g_uniex (syn_cfv (.cv g) (syn_csn (.cv b))) p0077
  have p0079 :=
    @g_fvmpt z (.cv b) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b)))) D (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0006 dv_cache_0007 dv_cache_0001 p0075 p0076 p0078
  have p0080 :=
    @g_syl (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (.classMem (.cv b) D) (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b))))) p0071 p0079
  have p0081 :=
    @g_eqcomd (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b)))) p0080
  have p0082 :=
    @g_breq12d (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b)))) (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) S p0068 p0081
  have p0083 :=
    @g_bitrd (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))) (syn_wbr (.cv a) R (.cv b)) (syn_wbr (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) S (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b))))) (syn_wbr (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) S (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) p0055 p0082
  have p0084 :=
    @g_ralrimivva (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wb (syn_wbr (.cv a) R (.cv b)) (syn_wbr (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) S (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))) a b D D dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0083
  have p0085 :=
    @g_jca (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E) (syn_wral a D (syn_wral b D (syn_wb (syn_wbr (.cv a) R (.cv b)) (syn_wbr (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) S (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))))) p0002 p0084
  have p0086 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso a b D E R S (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0012 dv_cache_0008 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0011
  have p0087 :=
    @g_biimpri (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E) (syn_wa (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E) (syn_wral a D (syn_wral b D (syn_wb (syn_wbr (.cv a) R (.cv b)) (syn_wbr (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) S (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))))))) p0086
  have p0088 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E) (syn_wral a D (syn_wral b D (syn_wb (syn_wbr (.cv a) R (.cv b)) (syn_wbr (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) S (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))))))) (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E) p0085 p0087
  exact p0088

noncomputable def g_sifvalimpclndv
    (C : Class) (D : Class) (E : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C)))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ E.fv ∪ F.fv
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_E : c ∉ E.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have dv_cache_0001 : c ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : c ∉ ((Wff.imp (.classMem C D) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, fresh_c_not_D, fresh_c_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : c ∉ ((syn_wa (syn_wf F D E) (.classMem C D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_D, fresh_c_not_E, fresh_c_not_F, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wf F D E) (.classMem C D)
  have p0001 :=
    @g_simpr (syn_wf F D E) (.classMem C D)
  have p0002 :=
    @g_elex C D
  have p0003 :=
    @g_syl (syn_wa (syn_wf F D E) (.classMem C D)) (.classMem C D) (.classMem C (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_simpr (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)
  have p0005 :=
    @g_eleq1 (.cv c) C D
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)) (.classEq (.cv c) C) (syn_wb (.classMem (.cv c) D) (.classMem C D)) p0004 p0005
  have p0007 :=
    @g_simpr (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)
  have p0008 :=
    @g_sneqd (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)) (.cv c) C p0007
  have p0009 :=
    @g_fveq2d (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)) (syn_csn (.cv c)) (syn_csn C) (syn_csi F) p0008
  have p0010 :=
    @g_simpr (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)
  have p0011 :=
    @g_fveq2d (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)) (.cv c) C F p0010
  have p0012 :=
    @g_sneqd (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)) (syn_cfv F (.cv c)) (syn_cfv F C) p0011
  have p0013 :=
    @g_eqeq12d (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)) (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F (.cv c))) (syn_csn (syn_cfv F C)) p0009 p0012
  have p0014 :=
    @g_imbi12d (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)) (.classMem (.cv c) D) (.classMem C D) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c)))) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))) p0006 p0013
  have p0015 :=
    @g_simpl (syn_wf F D E) (.classMem C D)
  have p0016 :=
    @g_simpl (syn_wf F D E) (.classMem (.cv c) D)
  have p0017 :=
    @g_ffn D E F
  have p0018 :=
    @g_syl (syn_wa (syn_wf F D E) (.classMem (.cv c) D)) (syn_wf F D E) (syn_wfn F D) p0016 p0017
  have p0019 :=
    @g_simpr (syn_wf F D E) (.classMem (.cv c) D)
  have p0020 :=
    @g_jca (syn_wa (syn_wf F D E) (.classMem (.cv c) D)) (syn_wfn F D) (.classMem (.cv c) D) p0018 p0019
  have p0021 :=
    @g_sifnvalv c D F
  have p0022 :=
    @g_syl (syn_wa (syn_wf F D E) (.classMem (.cv c) D)) (syn_wa (syn_wfn F D) (.classMem (.cv c) D)) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c)))) p0020 p0021
  have p0023 :=
    @g_ex (syn_wf F D E) (.classMem (.cv c) D) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c)))) p0022
  have p0024 :=
    @g_syl (syn_wa (syn_wf F D E) (.classMem C D)) (syn_wf F D E) (.imp (.classMem (.cv c) D) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))) p0015 p0023
  have p0025 :=
    @g_vtocld (syn_wa (syn_wf F D E) (.classMem C D)) (.imp (.classMem (.cv c) D) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))) (.imp (.classMem C D) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C)))) c C (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0003 p0014 p0024
  have p0026 :=
    @g_mpd (syn_wa (syn_wf F D E) (.classMem C D)) (.classMem C D) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))) p0000 p0025
  exact p0026

noncomputable def g_pw1sif1omapndv
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wf1o (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1of A B F
  have p0001 :=
    @g_sifmap A B F
  have p0002 :=
    @g_syl (syn_wf1o F A B) (syn_wf F A B) (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) p0000 p0001
  have p0003 :=
    @g_ffn (syn_cpw1 A) (syn_cpw1 B) (syn_csi F)
  have p0004 :=
    @g_syl (syn_wf1o F A B) (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) (syn_wfn (syn_csi F) (syn_cpw1 A)) p0002 p0003
  have p0005 :=
    @g_f1ocnv A B F
  have p0006 :=
    @g_f1of B A (syn_ccnv F)
  have p0007 :=
    @g_syl (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A) (syn_wf (syn_ccnv F) B A) p0005 p0006
  have p0008 :=
    @g_sifmap B A (syn_ccnv F)
  have p0009 :=
    @g_syl (syn_wf1o F A B) (syn_wf (syn_ccnv F) B A) (syn_wf (syn_csi (syn_ccnv F)) (syn_cpw1 B) (syn_cpw1 A)) p0007 p0008
  have p0010 :=
    @g_ffn (syn_cpw1 B) (syn_cpw1 A) (syn_csi (syn_ccnv F))
  have p0011 :=
    @g_syl (syn_wf1o F A B) (syn_wf (syn_csi (syn_ccnv F)) (syn_cpw1 B) (syn_cpw1 A)) (syn_wfn (syn_csi (syn_ccnv F)) (syn_cpw1 B)) p0009 p0010
  have p0012 :=
    @g_cnvsi F
  have p0013 :=
    @g_fneq1i (syn_cpw1 B) (syn_ccnv (syn_csi F)) (syn_csi (syn_ccnv F)) p0012
  have p0014 :=
    @g_sylibr (syn_wf1o F A B) (syn_wfn (syn_csi (syn_ccnv F)) (syn_cpw1 B)) (syn_wfn (syn_ccnv (syn_csi F)) (syn_cpw1 B)) p0011 p0013
  have p0015 :=
    @g_jca (syn_wf1o F A B) (syn_wfn (syn_csi F) (syn_cpw1 A)) (syn_wfn (syn_ccnv (syn_csi F)) (syn_cpw1 B)) p0004 p0014
  have p0016 :=
    @g_dff1o4 (syn_cpw1 A) (syn_cpw1 B) (syn_csi F)
  have p0017 :=
    @g_sylibr (syn_wf1o F A B) (syn_wa (syn_wfn (syn_csi F) (syn_cpw1 A)) (syn_wfn (syn_ccnv (syn_csi F)) (syn_cpw1 B))) (syn_wf1o (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) p0015 p0016
  exact p0017

#print axioms g_pw1sif1omapndv

end NFChoice.DirectNominalPrf.WPPReplay
