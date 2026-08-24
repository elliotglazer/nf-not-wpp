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
import NominalWPPReplayChunk015Compact001Part002

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

noncomputable def g_hwnisobaserestr
    (v : Var) (u : Var) (A : Class) (D : Class) (dv_u_v : u ≠ v) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (.imp (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwniso D) (.cv v)))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ D.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_v : h ≠ v := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_h : v ≠ h :=
    Ne.symm fresh_h_ne_v
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_h : u ≠ h :=
    Ne.symm fresh_h_ne_u
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ≠ v := by
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0002 : h ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0004 : h ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0005 : h ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0001 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0002 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)) p0001
  have p0003 :=
    @g_hwcnraw u D
  have p0004 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcodes D)) p0002 p0003
  have p0005 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0006 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D)) p0005
  have p0007 :=
    @g_hwcnraw v D
  have p0008 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv v) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcodes D)) p0006 p0007
  have p0009 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D)) p0004 p0008
  have p0010 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0011 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0012 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0011
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0010 p0012
  have p0014 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0013
  have p0015 :=
    @g_brhwisoany v u A h dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0016 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0014 p0016
  have p0018 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0017
  have p0019 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0009 p0018
  have p0020 :=
    @g_brhwisoany v u D h dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0021 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwiso D) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (.classMem (.cv v) (syn_chwcodes D))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wbr (.cv u) (syn_chwiso D) (.cv v)) p0019 p0021
  have p0023 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwiso D) (.cv v)) p0000 p0022
  have p0024 :=
    @g_hwnisohwisob v u D dv_cache_0001
  have p0025 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwiso D) (.cv v))) p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwiso D) (.cv v))) (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) p0023 p0025
  have p0027 :=
    @g_ex (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv v) (syn_chwcn D))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwniso D) (.cv v)) p0026
  exact p0027

noncomputable def g_hwnisobaserestrcl
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_D, fresh_y_not_C, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_ne_y, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))
  have p0001 :=
    @g_elex B (syn_chwcn D)
  have p0002 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.classMem B (syn_chwcn D)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))
  have p0004 :=
    @g_elex C (syn_chwcn D)
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.classMem C (syn_chwcn D)) (.classMem C (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_eleq1 (.cv x) B (syn_chwcn D)
  have p0008 :=
    @g_biid (.classMem (.cv y) (syn_chwcn D))
  have p0009 :=
    @g_a1i (syn_wb (.classMem (.cv y) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.classEq (.cv x) B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) (syn_chwcn D)) (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)) p0007 p0009
  have p0011 :=
    @g_breq1 (.cv x) B (.cv y) (syn_chwniso A)
  have p0012 :=
    @g_breq1 (.cv x) B (.cv y) (syn_chwniso D)
  have p0013 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr (.cv x) (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y)) p0011 p0012
  have p0014 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wa (.classMem (.cv x) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.imp (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr (.cv x) (syn_chwniso D) (.cv y))) (.imp (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y))) p0010 p0013
  have p0015 :=
    @g_biid (.classMem B (syn_chwcn D))
  have p0016 :=
    @g_a1i (syn_wb (.classMem B (syn_chwcn D)) (.classMem B (syn_chwcn D))) (.classEq (.cv y) C) p0015
  have p0017 :=
    @g_eleq1 (.cv y) C (syn_chwcn D)
  have p0018 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem B (syn_chwcn D)) (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)) (.classMem C (syn_chwcn D)) p0016 p0017
  have p0019 :=
    @g_breq2 (.cv y) C B (syn_chwniso A)
  have p0020 :=
    @g_breq2 (.cv y) C B (syn_chwniso D)
  have p0021 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso D) C) p0019 p0020
  have p0022 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y))) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C)) p0018 p0021
  have p0023 :=
    @g_hwnisobaserestr y x A D dv_cache_0001
  have p0024 :=
    @g_vtocl2g (.imp (syn_wa (.classMem (.cv x) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.imp (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr (.cv x) (syn_chwniso D) (.cv y)))) (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y)))) (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C))) x y B C (syn_cvv) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0014 p0022 p0023
  have p0025 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C))) p0006 p0024
  have p0026 :=
    @g_pm2_43i (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C)) p0025
  exact p0026

noncomputable def g_brlnqrelg
    (x : Var) (y : Var) (C : Class) (D : Class) (R : Class) (V : Class) (W : Class) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (.classMem C V) (.classMem D W)) (syn_wb (syn_wbr C (syn_clnqrel R) D) (syn_wrex x C (syn_wrex y D (syn_wbr (.cv x) R (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv ∪ V.fv ∪ W.fv
  let b : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_V : b ∉ V.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_W : b ∉ W.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_D : a ∉ D.fv := by
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
  have fresh_b_ne_a : b ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_b : a ≠ b :=
    Ne.symm fresh_b_ne_a
  have dv_cache_0001 : x ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv b) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0011 : a ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0012 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0013 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0014 : b ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0015 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0016 : a ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : b ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : a ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : b ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((syn_wrex x C (syn_wrex y D (syn_wbr (.cv x) R (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_C, fresh_a_not_D, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : b ∉ ((syn_wrex x C (syn_wrex y D (syn_wbr (.cv x) R (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_C, fresh_b_not_D, fresh_b_ne_x, fresh_b_ne_y, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_rexeq (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y))) x (.cv a) C dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_rexeq (syn_wbr (.cv x) R (.cv y)) y (.cv b) D dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_rexbidv (.classEq (.cv b) D) (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y))) (syn_wrex y D (syn_wbr (.cv x) R (.cv y))) x C dv_cache_0005 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lnqrel x y R a b dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0004 :=
    @g_brabg (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y)))) (syn_wrex x C (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y)))) (syn_wrex x C (syn_wrex y D (syn_wbr (.cv x) R (.cv y)))) a b C D V W (syn_clnqrel R) dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0010 p0000 p0002 p0003
  exact p0004

noncomputable def g_ellnkerec
    (u : Var) (R : Class) (X : Class) :
    Nominal.NPrf (syn_wb (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ R.fv ∪ X.fv
  have p0000 :=
    @g_elec (.cv u) X (syn_clnker R)
  have p0001 :=
    @g_brlnker R X (.cv u)
  have p0002 :=
    @g_bitri (.classMem (.cv u) (syn_cec X (syn_clnker R))) (syn_wbr X (syn_clnker R) (.cv u)) (syn_wa (syn_wbr X R (.cv u)) (syn_wbr (.cv u) R X)) p0000 p0001
  exact p0002

noncomputable def g_ellnkerecg
    (B : Class) (C : Class) (R : Class) :
    Nominal.NPrf (syn_wb (.classMem B (syn_cec C (syn_clnker R))) (syn_wa (syn_wbr C R B) (syn_wbr B R C))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ R.fv
  have p0000 :=
    @g_elec B C (syn_clnker R)
  have p0001 :=
    @g_brlnker R C B
  have p0002 :=
    @g_bitri (.classMem B (syn_cec C (syn_clnker R))) (syn_wbr C (syn_clnker R) B) (syn_wa (syn_wbr C R B) (syn_wbr B R C)) p0000 p0001
  exact p0002

#print axioms g_ellnkerecg

end NFChoice.DirectNominalPrf.WPPReplay
