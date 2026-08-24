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
import NominalWPPReplayChunk014Compact001Part039

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

noncomputable def g_hwnisosymi
    (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf (.imp (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ≠ v := by
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show v ≠ u from (by exact Ne.symm dv_u_v))
  have p0000 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0001 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0000
  have p0002 :=
    @g_simpld (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0001
  have p0003 :=
    @g_ancom (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0004 :=
    @g_biimpi (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0003
  have p0005 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0002 p0004
  have p0006 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0007 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0006
  have p0008 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0007
  have p0009 :=
    @g_hwisosymi v u A dv_cache_0002 dv_cache_0003 dv_cache_0001
  have p0010 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv u)) p0008 p0009
  have p0011 :=
    @g_jca (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv u)) p0005 p0010
  have p0012 :=
    @g_hwnisohwisob u v A dv_cache_0004
  have p0013 :=
    @g_biimpri (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv u))) p0012
  have p0014 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) p0011 p0013
  exact p0014

noncomputable def g_hwnisotri
    (w : Var) (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) (dv_u_v : u ≠ v) (dv_u_w : u ≠ w) (dv_v_w : v ≠ w) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chwniso A) (.cv w))) := by
  let proofSupport : Finset Var := ({w} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ≠ v := by
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0002 : v ≠ w := by
    clear dv_cache_0001
    exact (show v ≠ w from (by exact dv_v_w))
  have dv_cache_0003 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ w from (by exact dv_u_w))
  have p0000 :=
    @g_simpl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0001 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0002 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0001
  have p0003 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0000 p0002
  have p0004 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0005 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0003 p0004
  have p0006 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0007 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0005 p0006
  have p0008 :=
    @g_simpr (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0009 :=
    @g_hwnisohwisob w v A dv_cache_0002
  have p0010 :=
    @g_biimpi (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) p0009
  have p0011 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) p0008 p0010
  have p0012 :=
    @g_simpl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
  have p0013 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) p0011 p0012
  have p0014 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))
  have p0015 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0013 p0014
  have p0016 :=
    @g_jca (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0007 p0015
  have p0017 :=
    @g_simpl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0018 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0019 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0018
  have p0020 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0017 p0019
  have p0021 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0022 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0020 p0021
  have p0023 :=
    @g_simpr (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0024 :=
    @g_hwnisohwisob w v A dv_cache_0002
  have p0025 :=
    @g_biimpi (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) p0023 p0025
  have p0027 :=
    @g_simpr (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
  have p0028 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w)) p0026 p0027
  have p0029 :=
    @g_jca (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w)) p0022 p0028
  have p0030 :=
    @g_hwisotri w v u A dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0001 dv_cache_0006 dv_cache_0002
  have p0031 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0029 p0030
  have p0032 :=
    @g_jca (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0016 p0031
  have p0033 :=
    @g_hwnisohwisob w u A dv_cache_0006
  have p0034 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w))) p0033
  have p0035 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w))) (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) p0032 p0034
  exact p0035

noncomputable def g_hwnisoer
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A))) := by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
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
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_u_ne_w : u ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_u : w ≠ u :=
    Ne.symm fresh_u_ne_w
  have fresh_v_ne_w : v ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_v : w ≠ v :=
    Ne.symm fresh_v_ne_w
  have dv_cache_0001 : u ≠ v := by
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0005 : v ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have dv_cache_0006 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0008 : u ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : v ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : v ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : u ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : v ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : w ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chwniso] using (Nominal.classEqRefl (syn_chwniso A)))
  have p0001 :=
    @g_hwgenex
  have p0002 :=
    @g_hwbijex
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0002 p0003
  have p0005 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_a1i (.classMem (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)) (.classMem A (syn_cvv)) p0005
  have p0007 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0008 :=
    @g_hwcodesexg A (syn_cvv)
  have p0009 :=
    @g_hwrelsex
  have p0010 :=
    @g_a1i (.classMem (syn_chwrels) (syn_cvv)) (.classMem A (syn_cvv)) p0009
  have p0011 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwcodes A) (syn_cvv)) (.classMem (syn_chwrels) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_inexg (syn_chwcodes A) (syn_chwrels) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chwcodes A) (syn_cvv)) (.classMem (syn_chwrels) (syn_cvv))) (.classMem (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv) p0007 p0013
  have p0015 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0016 :=
    @g_hwcodesexg A (syn_cvv)
  have p0017 :=
    @g_hwrelsex
  have p0018 :=
    @g_a1i (.classMem (syn_chwrels) (syn_cvv)) (.classMem A (syn_cvv)) p0017
  have p0019 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwcodes A) (syn_cvv)) (.classMem (syn_chwrels) (syn_cvv)) p0016 p0018
  have p0020 :=
    @g_inexg (syn_chwcodes A) (syn_chwrels) (syn_cvv) (syn_cvv)
  have p0021 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chwcodes A) (syn_cvv)) (.classMem (syn_chwrels) (syn_cvv))) (.classMem (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv) p0015 p0021
  have p0023 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0014 p0022
  have p0024 :=
    @g_xpexg (syn_chwcn A) (syn_chwcn A) (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chwcn A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (.classMem (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)) (.classMem (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv)) p0006 p0025
  have p0027 :=
    @g_inexg (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv) (syn_cvv)
  have p0028 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)) (.classMem (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv))) (.classMem (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_cvv)) p0026 p0027
  have p0029 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_cvv) p0000 p0028
  have p0030 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0031 :=
    @g_hwcodesexg A (syn_cvv)
  have p0032 :=
    @g_hwrelsex
  have p0033 :=
    @g_a1i (.classMem (syn_chwrels) (syn_cvv)) (.classMem A (syn_cvv)) p0032
  have p0034 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwcodes A) (syn_cvv)) (.classMem (syn_chwrels) (syn_cvv)) p0031 p0033
  have p0035 :=
    @g_inexg (syn_chwcodes A) (syn_chwrels) (syn_cvv) (syn_cvv)
  have p0036 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chwcodes A) (syn_cvv)) (.classMem (syn_chwrels) (syn_cvv))) (.classMem (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv)) p0034 p0035
  have p0037 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv) p0030 p0036
  have p0038 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0039 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0038
  have p0040 :=
    @g_simpld (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0039
  have p0041 :=
    @g_ancom (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0042 :=
    @g_biimpi (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0041
  have p0043 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0040 p0042
  have p0044 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0045 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0044
  have p0046 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0045
  have p0047 :=
    @g_hwisosymi v u A dv_cache_0002 dv_cache_0003 dv_cache_0001
  have p0048 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv u)) p0046 p0047
  have p0049 :=
    @g_jca (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv u)) p0043 p0048
  have p0050 :=
    @g_hwnisohwisob u v A dv_cache_0004
  have p0051 :=
    @g_biimpri (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv u))) p0050
  have p0052 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) p0049 p0051
  have p0053 :=
    @g_n_3ad2ant3 (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem A (syn_cvv)) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0052
  have p0054 :=
    @g_simpl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0055 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0056 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0054 p0056
  have p0058 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0059 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0057 p0058
  have p0060 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0061 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0059 p0060
  have p0062 :=
    @g_simpr (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0063 :=
    @g_hwnisohwisob w v A dv_cache_0005
  have p0064 :=
    @g_biimpi (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) p0063
  have p0065 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) p0062 p0064
  have p0066 :=
    @g_simpl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
  have p0067 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) p0065 p0066
  have p0068 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))
  have p0069 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0067 p0068
  have p0070 :=
    @g_jca (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0061 p0069
  have p0071 :=
    @g_simpl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0072 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0073 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0072
  have p0074 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0071 p0073
  have p0075 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0076 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0074 p0075
  have p0077 :=
    @g_simpr (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0078 :=
    @g_hwnisohwisob w v A dv_cache_0005
  have p0079 :=
    @g_biimpi (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) p0078
  have p0080 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) p0077 p0079
  have p0081 :=
    @g_simpr (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
  have p0082 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wbr (.cv v) (syn_chwiso A) (.cv w)) p0080 p0081
  have p0083 :=
    @g_jca (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w)) p0076 p0082
  have p0084 :=
    @g_hwisotri w v u A dv_cache_0002 dv_cache_0003 dv_cache_0006 dv_cache_0001 dv_cache_0007 dv_cache_0005
  have p0085 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0083 p0084
  have p0086 :=
    @g_jca (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0070 p0085
  have p0087 :=
    @g_hwnisohwisob w u A dv_cache_0007
  have p0088 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w))) p0087
  have p0089 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w))) (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) p0086 p0088
  have p0090 :=
    @g_n_3ad2ant3 (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) p0089
  have p0091 :=
    @g_iserd (.classMem A (syn_cvv)) u v w (syn_chwcn A) (syn_chwniso A) (syn_cvv) (syn_cvv) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0001 dv_cache_0007 dv_cache_0005 p0029 p0037 p0053 p0090
  exact p0091

noncomputable def g_hwnisorefli
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ≠ v := by
    clear dv_cache_0001
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0003 : v ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pm4_24 (.classMem (.cv u) (syn_chwcn A))
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0000
  have p0002 :=
    @g_hwcnraw u A
  have p0003 :=
    @g_hwisorefl u A dv_cache_0001
  have p0004 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0002 p0003
  have p0005 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0001 p0004
  have p0006 :=
    @g_elex (.cv u) (syn_chwcn A)
  have p0007 :=
    @g_breq2 (.cv v) (.cv u) (.cv u) (syn_chwniso A)
  have p0008 :=
    @g_eleq1 (.cv v) (.cv u) (syn_chwcn A)
  have p0009 :=
    @g_anbi2d (.classEq (.cv v) (.cv u)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0008
  have p0010 :=
    @g_breq2 (.cv v) (.cv u) (.cv u) (syn_chwiso A)
  have p0011 :=
    @g_anbi12d (.classEq (.cv v) (.cv u)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0009 p0010
  have p0012 :=
    @g_bibi12d (.classEq (.cv v) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))) p0007 p0011
  have p0013 :=
    @g_hwnisohwisob v u A dv_cache_0002
  have p0014 :=
    @g_vtoclg (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))) (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)))) v (.cv u) (syn_cvv) dv_cache_0003 dv_cache_0004 p0012 p0013
  have p0015 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv)) (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u)))) p0006 p0014
  have p0016 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))) p0005 p0015
  exact p0016

noncomputable def g_hwnisoerv
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
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
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_u_ne_w : u ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_u : w ≠ u :=
    Ne.symm fresh_u_ne_w
  have fresh_v_ne_w : v ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_v : w ≠ v :=
    Ne.symm fresh_v_ne_w
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0004 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0006 : v ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have dv_cache_0007 : u ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : v ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : u ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : v ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hwnisoexg A
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_a1i (.classMem (syn_cvv) (syn_cvv)) (.classMem A (syn_cvv)) p0001
  have p0003 :=
    @g_hwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_n_3ad2ant3 (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem A (syn_cvv)) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (.cv v) (syn_cvv))) p0003
  have p0005 :=
    @g_hwnisotri w v u A dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0003 dv_cache_0005 dv_cache_0006
  have p0006 :=
    @g_n_3ad2ant3 (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_w3a (.classMem (.cv u) (syn_cvv)) (.classMem (.cv v) (syn_cvv)) (.classMem (.cv w) (syn_cvv))) p0005
  have p0007 :=
    @g_iserd (.classMem A (syn_cvv)) u v w (syn_cvv) (syn_chwniso A) (syn_cvv) (syn_cvv) dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0003 dv_cache_0005 dv_cache_0006 p0000 p0002 p0004 p0006
  exact p0007

#print axioms g_hwnisoerv

end NFChoice.DirectNominalPrf.WPPReplay
