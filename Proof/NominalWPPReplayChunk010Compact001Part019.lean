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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk010Compact001Part018

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

noncomputable def g_sfin111
    (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.classEq M N)) := by
  let proofSupport : Finset Var := P.fv ∪ M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_P : a ∉ P.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : a ∉ (N).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (P).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((syn_wne M (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin N P a dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_simp2bi (syn_wsfin N P) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) N) (.classMem (syn_cpw (.cv a)) P))) p0000
  have p0002 :=
    @g_adantl (syn_wsfin N P) (.classMem P (syn_cnnc)) (syn_wsfin M P) p0001
  have p0003 :=
    @g_ltfinirr P
  have p0004 :=
    @g_syl (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.classMem P (syn_cnnc)) (.neg (.classMem (syn_copk P P) (syn_cltfin))) p0002 p0003
  have p0005 :=
    @g_sfinltfin N P M P
  have p0006 :=
    @g_mtand (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk P P) (syn_cltfin)) p0004 p0005
  have p0007 :=
    @g_sfinltfin M P N P
  have p0008 :=
    @g_ex (syn_wa (syn_wsfin N P) (syn_wsfin M P)) (.classMem (syn_copk N M) (syn_cltfin)) (.classMem (syn_copk P P) (syn_cltfin)) p0007
  have p0009 :=
    @g_ancoms (syn_wsfin N P) (syn_wsfin M P) (.imp (.classMem (syn_copk N M) (syn_cltfin)) (.classMem (syn_copk P P) (syn_cltfin))) p0008
  have p0010 :=
    @g_mtod (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.classMem (syn_copk N M) (syn_cltfin)) (.classMem (syn_copk P P) (syn_cltfin)) p0004 p0009
  have p0011 :=
    @g_ioran (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin))
  have p0012 :=
    @g_sylanbrc (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.neg (.classMem (syn_copk M N) (syn_cltfin))) (.neg (.classMem (syn_copk N M) (syn_cltfin))) (.neg (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)))) p0006 p0010 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M P a dv_cache_0003 dv_cache_0002
  have p0014 :=
    @g_simp1bi (syn_wsfin M P) (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) P))) p0013
  have p0015 :=
    @g_adantr (syn_wsfin M P) (.classMem M (syn_cnnc)) (syn_wsfin N P) p0014
  have p0016 :=
    @g_simp1bi (syn_wsfin N P) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) N) (.classMem (syn_cpw (.cv a)) P))) p0000
  have p0017 :=
    @g_adantl (syn_wsfin N P) (.classMem N (syn_cnnc)) (syn_wsfin M P) p0016
  have p0018 :=
    @g_ne0i M (syn_cpw1 (.cv a))
  have p0019 :=
    @g_adantr (.classMem (syn_cpw1 (.cv a)) M) (syn_wne M (syn_c0)) (.classMem (syn_cpw (.cv a)) P) p0018
  have p0020 :=
    @g_exlimiv (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) P)) (syn_wne M (syn_c0)) a dv_cache_0004 p0019
  have p0021 :=
    @g_n_3ad2ant3 (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) P))) (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (.classMem P (syn_cnnc)) p0020
  have p0022 :=
    @g_sylbi (syn_wsfin M P) (syn_w3a (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) P)))) (syn_wne M (syn_c0)) p0013 p0021
  have p0023 :=
    @g_adantr (syn_wsfin M P) (syn_wne M (syn_c0)) (syn_wsfin N P) p0022
  have p0024 :=
    @g_ltfintri M N
  have p0025 :=
    @g_syl3anc (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin))) p0015 p0017 p0023 p0024
  have p0026 :=
    (by simpa [syn_wb, syn_w3o] using (Nominal.biimpRefl (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin)))))
  have p0027 :=
    @g_sylib (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin))) (syn_wo (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)) (.classMem (syn_copk N M) (syn_cltfin))) p0025 p0026
  have p0028 :=
    @g_or32 (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin))
  have p0029 :=
    @g_sylib (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (syn_wo (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)) (.classMem (syn_copk N M) (syn_cltfin))) (syn_wo (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin))) (.classEq M N)) p0027 p0028
  have p0030 :=
    @g_orel1 (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin))) (.classEq M N)
  have p0031 :=
    @g_sylc (syn_wa (syn_wsfin M P) (syn_wsfin N P)) (.neg (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)))) (syn_wo (syn_wo (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin))) (.classEq M N)) (.classEq M N) p0012 p0029 p0030
  exact p0031

#print axioms g_sfin111

end NFChoice.DirectNominalPrf.WPPReplay
