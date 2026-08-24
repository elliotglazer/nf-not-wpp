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
import NominalWPPReplayChunk017Compact001Part039

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

noncomputable def g_hncodecmpstrictbrndv
    (x : Var) (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb (syn_wbr (.cv u) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_v_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0008 : v ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show v ≠ x from (by exact dv_v_x))
  have p0000 :=
    @g_brdif (.cv u) (.cv v) (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))
  have p0001 :=
    @g_brcnv (.cv u) (.cv v) (syn_chncodecmpset A)
  have p0002 :=
    @g_notbii (syn_wbr (.cv u) (syn_ccnv (syn_chncodecmpset A)) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0001
  have p0003 :=
    @g_anbi2i (.neg (syn_wbr (.cv u) (syn_ccnv (syn_chncodecmpset A)) (.cv v))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) p0002
  have p0004 :=
    @g_bitri (syn_wbr (.cv u) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv u) (syn_ccnv (syn_chncodecmpset A)) (.cv v)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))) p0000 p0003
  have p0005 :=
    @g_a1i (syn_wb (syn_wbr (.cv u) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) p0004
  have p0006 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
  have p0007 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0006
  have p0008 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
  have p0009 :=
    @g_hncodecmpkerptndv v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0010 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) p0008 p0009
  have p0011 :=
    @g_biimprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0010
  have p0012 :=
    @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0013 :=
    @g_biimpi (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0012
  have p0014 :=
    @g_syl6 (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0011 p0013
  have p0015 :=
    @g_simpr (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))
  have p0016 :=
    @g_syl6 (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0014 p0015
  have p0017 :=
    @g_mtod (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0007 p0016
  have p0018 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
  have p0019 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0018
  have p0020 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))
  have p0021 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0020 p0021
  have p0023 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0024 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0022 p0023
  have p0025 :=
    @g_mpbid (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0019 p0024
  have p0026 :=
    @g_orcanai (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0025
  have p0027 :=
    @g_mpdan (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) (.neg (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0017 p0026
  have p0028 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0029 :=
    @g_olc (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0030 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0028 p0029
  have p0031 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0032 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0031 p0032
  have p0034 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0035 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0033 p0034
  have p0036 :=
    @g_mpbird (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0030 p0035
  have p0037 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0038 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0039 :=
    @g_hncodecmpstrictnoreversendv x v u A dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0007 dv_cache_0008
  have p0040 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.imp (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))) p0038 p0039
  have p0041 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0037 p0040
  have p0042 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0036 p0041
  have p0043 :=
    @g_impbida (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0027 p0042
  have p0044 :=
    @g_bitrd (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0005 p0043
  exact p0044

noncomputable def g_hncodecutfnex
     :
    Nominal.NPrf (.classMem (syn_chncodecutfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_chncodecutfn] using (Nominal.classEqRefl (syn_chncodecutfn)))
  have p0001 :=
    (by simpa [syn_chncoderelfn] using (Nominal.classEqRefl (syn_chncoderelfn)))
  have p0002 :=
    @g_lninteropex
  have p0003 :=
    @g_n_1stex
  have p0004 :=
    @g_n_1stex
  have p0005 :=
    @g_coex (syn_c1st) (syn_c1st) p0003 p0004
  have p0006 :=
    (by simpa [syn_chncodesquarefn] using (Nominal.classEqRefl (syn_chncodesquarefn)))
  have p0007 :=
    @g_crossex
  have p0008 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0009 :=
    @g_lninteropex
  have p0010 :=
    @g_n_2ndex
  have p0011 :=
    @g_n_1stex
  have p0012 :=
    @g_coex (syn_c2nd) (syn_c1st) p0010 p0011
  have p0013 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0014 :=
    @g_lnimageopex
  have p0015 :=
    @g_swapex
  have p0016 :=
    @g_imageex (syn_cswap) p0015
  have p0017 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0018 :=
    @g_lndifopex
  have p0019 :=
    @g_n_1stex
  have p0020 :=
    @g_n_1stex
  have p0021 :=
    @g_coex (syn_c1st) (syn_c1st) p0019 p0020
  have p0022 :=
    @g_vvex
  have p0023 :=
    @g_snex (syn_cid)
  have p0024 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cid)) p0022 p0023
  have p0025 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p0021 p0024
  have p0026 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0018 p0025
  have p0027 :=
    @g_eqeltri (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv) p0017 p0026
  have p0028 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0016 p0027
  have p0029 :=
    @g_n_2ndex
  have p0030 :=
    @g_txpex (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0028 p0029
  have p0031 :=
    @g_coex (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0014 p0030
  have p0032 :=
    @g_eqeltri (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv) p0013 p0031
  have p0033 :=
    @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0012 p0032
  have p0034 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0009 p0033
  have p0035 :=
    @g_eqeltri (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv) p0008 p0034
  have p0036 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0037 :=
    @g_lninteropex
  have p0038 :=
    @g_n_2ndex
  have p0039 :=
    @g_n_1stex
  have p0040 :=
    @g_coex (syn_c2nd) (syn_c1st) p0038 p0039
  have p0041 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0042 :=
    @g_lnimageopex
  have p0043 :=
    @g_swapex
  have p0044 :=
    @g_imageex (syn_cswap) p0043
  have p0045 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0046 :=
    @g_lndifopex
  have p0047 :=
    @g_n_1stex
  have p0048 :=
    @g_n_1stex
  have p0049 :=
    @g_coex (syn_c1st) (syn_c1st) p0047 p0048
  have p0050 :=
    @g_vvex
  have p0051 :=
    @g_snex (syn_cid)
  have p0052 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cid)) p0050 p0051
  have p0053 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p0049 p0052
  have p0054 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0046 p0053
  have p0055 :=
    @g_eqeltri (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv) p0045 p0054
  have p0056 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0044 p0055
  have p0057 :=
    @g_n_2ndex
  have p0058 :=
    @g_txpex (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0056 p0057
  have p0059 :=
    @g_coex (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0042 p0058
  have p0060 :=
    @g_eqeltri (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv) p0041 p0059
  have p0061 :=
    @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0040 p0060
  have p0062 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0037 p0061
  have p0063 :=
    @g_eqeltri (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv) p0036 p0062
  have p0064 :=
    @g_txpex (syn_chncodecarrierfn) (syn_chncodecarrierfn) p0035 p0063
  have p0065 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0007 p0064
  have p0066 :=
    @g_eqeltri (syn_chncodesquarefn) (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) (syn_cvv) p0006 p0065
  have p0067 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn) p0005 p0066
  have p0068 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0002 p0067
  have p0069 :=
    @g_eqeltri (syn_chncoderelfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cvv) p0001 p0068
  have p0070 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0071 :=
    @g_lninteropex
  have p0072 :=
    @g_n_2ndex
  have p0073 :=
    @g_n_1stex
  have p0074 :=
    @g_coex (syn_c2nd) (syn_c1st) p0072 p0073
  have p0075 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0076 :=
    @g_lnimageopex
  have p0077 :=
    @g_swapex
  have p0078 :=
    @g_imageex (syn_cswap) p0077
  have p0079 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0080 :=
    @g_lndifopex
  have p0081 :=
    @g_n_1stex
  have p0082 :=
    @g_n_1stex
  have p0083 :=
    @g_coex (syn_c1st) (syn_c1st) p0081 p0082
  have p0084 :=
    @g_vvex
  have p0085 :=
    @g_snex (syn_cid)
  have p0086 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cid)) p0084 p0085
  have p0087 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p0083 p0086
  have p0088 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0080 p0087
  have p0089 :=
    @g_eqeltri (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv) p0079 p0088
  have p0090 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0078 p0089
  have p0091 :=
    @g_n_2ndex
  have p0092 :=
    @g_txpex (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0090 p0091
  have p0093 :=
    @g_coex (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0076 p0092
  have p0094 :=
    @g_eqeltri (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv) p0075 p0093
  have p0095 :=
    @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0074 p0094
  have p0096 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0071 p0095
  have p0097 :=
    @g_eqeltri (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv) p0070 p0096
  have p0098 :=
    @g_txpex (syn_chncoderelfn) (syn_chncodecarrierfn) p0069 p0097
  have p0099 :=
    @g_eqeltri (syn_chncodecutfn) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv) p0000 p0098
  exact p0099

noncomputable def g_hncodepredinputsexg
    (v : Var) (A : Class) (X : Class) (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_chncodepredinputs A X v) (syn_cvv))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ A.fv ∪ X.fv
  have p0000 :=
    @g_snex (.cv v)
  have p0001 :=
    @g_fvex (.cv v) (syn_c2nd)
  have p0002 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (.cv v)) p0001
  have p0003 :=
    @g_xpex (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) p0000 p0002
  have p0004 :=
    @g_a1i (.classMem (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) p0003
  have p0005 :=
    @g_hncodecutfnex
  have p0006 :=
    @g_cnvexg (syn_chncodecutfn) (syn_cvv)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_a1i (.classMem (syn_ccnv (syn_chncodecutfn)) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) p0007
  have p0009 :=
    @g_simpl (.classMem A (syn_cvv)) (.classMem X (syn_cvv))
  have p0010 :=
    @g_hwnisoexg A
  have p0011 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_simpr (.classMem A (syn_cvv)) (.classMem X (syn_cvv))
  have p0013 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_chwniso A) (syn_cvv)) (.classMem X (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_imaexg (syn_chwniso A) X (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (.classMem (syn_chwniso A) (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_cima (syn_chwniso A) X) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_ccnv (syn_chncodecutfn)) (syn_cvv)) (.classMem (syn_cima (syn_chwniso A) X) (syn_cvv)) p0008 p0015
  have p0017 :=
    @g_imaexg (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X) (syn_cvv) (syn_cvv)
  have p0018 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (.classMem (syn_ccnv (syn_chncodecutfn)) (syn_cvv)) (.classMem (syn_cima (syn_chwniso A) X) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)) (syn_cvv)) p0016 p0017
  have p0019 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)) (syn_cvv)) p0004 p0018
  have p0020 :=
    @g_inexg (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)) (syn_cvv) (syn_cvv)
  have p0021 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (.classMem (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)) (syn_cvv))) (.classMem (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (syn_cvv)) p0019 p0020
  have p0022 :=
    (by simpa [syn_chncodepredinputs] using (Nominal.classEqRefl (syn_chncodepredinputs A X v)))
  have p0023 :=
    @g_eleq1i (syn_chncodepredinputs A X v) (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (syn_cvv) p0022
  have p0024 :=
    @g_sylibr (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (syn_cvv)) (.classMem (syn_chncodepredinputs A X v) (syn_cvv)) p0021 p0023
  exact p0024

noncomputable def g_hncodepredinputsssndv
    (v : Var) (A : Class) (X : Class) (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf (syn_wss (syn_chncodepredinputs A X v) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ A.fv ∪ X.fv
  have p0000 :=
    (by simpa [syn_chncodepredinputs] using (Nominal.classEqRefl (syn_chncodepredinputs A X v)))
  have p0001 :=
    @g_inss1 (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))
  have p0002 :=
    @g_eqsstri (syn_chncodepredinputs A X v) (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0000 p0001
  exact p0002

noncomputable def g_hncodepredinputmemndv
    (x : Var) (v : Var) (u : Var) (A : Class) (X : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_X_u : u ∉ X.fv) (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) :
    Nominal.NPrf (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ X.fv
  have dv_cache_0001 : v ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_u_x, dv_u_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chncodepredinputs] using (Nominal.classEqRefl (syn_chncodepredinputs A X v)))
  have p0001 :=
    @g_eleq2i (syn_chncodepredinputs A X v) (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (syn_cop (.cv v) (syn_csn (.cv x))) p0000
  have p0002 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))))) (.classMem (.cv v) (syn_chwcn A)) p0001
  have p0003 :=
    @g_elin (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))
  have p0004 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))) (syn_wa (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))))) (.classMem (.cv v) (syn_chwcn A)) p0003
  have p0005 :=
    @g_opelxp (.cv v) (syn_csn (.cv x)) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0006 :=
    @g_vex v
  have p0007 :=
    @g_snid (.cv v) p0006
  have p0008 :=
    @g_biantrur (.classMem (.cv v) (syn_csn (.cv v))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0007
  have p0009 :=
    @g_bicomi (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (.classMem (.cv v) (syn_csn (.cv v))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0008
  have p0010 :=
    @g_bitri (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (.cv v) (syn_csn (.cv v))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0005 p0009
  have p0011 :=
    @g_snelpw1 (.cv x) (syn_cfv (syn_c2nd) (.cv v))
  have p0012 :=
    @g_bitri (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0010 p0011
  have p0013 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (.cv v) (syn_chwcn A)) p0012
  have p0014 :=
    @g_hncodecutfnfn
  have p0015 :=
    @g_elpreima (syn_cvv) (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cima (syn_chwniso A) X) (syn_chncodecutfn)
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_vex v
  have p0018 :=
    @g_snex (.cv x)
  have p0019 :=
    @g_opex (.cv v) (syn_csn (.cv x)) p0017 p0018
  have p0020 :=
    @g_biantrur (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cvv)) (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_cima (syn_chwniso A) X)) p0019
  have p0021 :=
    @g_bicomi (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_cima (syn_chwniso A) X)) (syn_wa (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cvv)) (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_cima (syn_chwniso A) X))) p0020
  have p0022 :=
    @g_bitri (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (syn_wa (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cvv)) (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_cima (syn_chwniso A) X))) (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_cima (syn_chwniso A) X)) p0016 p0021
  have p0023 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_cima (syn_chwniso A) X))) (.classMem (.cv v) (syn_chwcn A)) p0022
  have p0024 :=
    @g_hncodecutfnvalhwcn x v A dv_cache_0001
  have p0025 :=
    @g_eleq1d (.classMem (.cv v) (syn_chwcn A)) (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cima (syn_chwniso A) X) p0024
  have p0026 :=
    @g_bitrd (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_cima (syn_chwniso A) X)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cima (syn_chwniso A) X)) p0023 p0025
  have p0027 :=
    @g_elima u (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) X dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0028 :=
    @g_a1i (syn_wb (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cima (syn_chwniso A) X)) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv v) (syn_chwcn A)) p0027
  have p0029 :=
    @g_bitrd (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cima (syn_chwniso A) X)) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0026 p0028
  have p0030 :=
    @g_anbi12d (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0013 p0029
  have p0031 :=
    @g_bitrd (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))) (syn_wa (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0004 p0030
  have p0032 :=
    @g_bitrd (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodepredinputs A X v)) (.classMem (syn_cop (.cv v) (syn_csn (.cv x))) (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0002 p0031
  exact p0032

noncomputable def g_hncodepredendsexg
    (v : Var) (A : Class) (X : Class) (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_chncodepredends A X v) (syn_cvv))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ A.fv ∪ X.fv
  have dv_cache_0001 : v ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_2ndex
  have p0001 :=
    @g_a1i (.classMem (syn_c2nd) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) p0000
  have p0002 :=
    @g_hncodepredinputsexg v A X dv_cache_0001
  have p0003 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_c2nd) (syn_cvv)) (.classMem (syn_chncodepredinputs A X v) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_imaexg (syn_c2nd) (syn_chncodepredinputs A X v) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (syn_wa (.classMem (syn_c2nd) (syn_cvv)) (.classMem (syn_chncodepredinputs A X v) (syn_cvv))) (.classMem (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_uniexg (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v)) (syn_cvv)
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v)) (syn_cvv)) (.classMem (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))) (syn_cvv)) p0005 p0006
  have p0008 :=
    (by simpa [syn_chncodepredends] using (Nominal.classEqRefl (syn_chncodepredends A X v)))
  have p0009 :=
    @g_eleq1i (syn_chncodepredends A X v) (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))) (syn_cvv) p0008
  have p0010 :=
    @g_sylibr (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv))) (.classMem (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v))) (syn_cvv)) (.classMem (syn_chncodepredends A X v) (syn_cvv)) p0007 p0009
  exact p0010

#print axioms g_hncodepredendsexg

end NFChoice.DirectNominalPrf.WPPReplay
