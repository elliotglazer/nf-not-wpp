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
import NominalWPPReplayChunk017Compact001Part077

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

noncomputable def g_hnwcutambordbrproxyimpndv
    (u : Var) (A : Class) (r : Var) (q : Var) (p : Var) (dv_A_p : p ∉ A.fv) (dv_A_q : q ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_p_q : p ≠ q) (dv_p_r : p ≠ r) (dv_p_u : p ≠ u) (dv_q_r : q ≠ r) (dv_q_u : q ≠ u) (dv_r_u : r ≠ u) (hyp_hnwcutambordbrproxyimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ ({r} : Finset Var) ∪ ({q} : Finset Var) ∪ ({p} : Finset Var)
  have dv_cache_0001 : p ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_p_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show p ≠ u from (by exact dv_p_u))
  have dv_cache_0006 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show q ≠ u from (by exact dv_q_u))
  have p0000 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0001 :=
    @g_pw12si2brndv (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) q p dv_cache_0001
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (.cv u)) (syn_cuni (syn_cuni (.cv q))))) p0000 p0001
  have p0003 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) hyp_hnwcutambordbrproxyimpndv_1
  have p0004 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0005 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0006 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0004 p0005
  have p0007 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0008 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0007 p0008
  have p0010 :=
    @g_pw12argcl (.cv p) (syn_cfv (syn_c2nd) (.cv u))
  have p0011 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))))) p0009 p0010
  have p0012 :=
    @g_simpld (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))) p0011
  have p0013 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0014 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
  have p0015 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0013 p0014
  have p0016 :=
    @g_pw12argcl (.cv q) (syn_cfv (syn_c2nd) (.cv u))
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0015 p0016
  have p0018 :=
    @g_simpld (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0017
  have p0019 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))) p0012 p0018
  have p0020 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u)))) p0006 p0019
  have p0021 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))))) p0003 p0020
  have p0022 :=
    @g_hnwcutcodecmpbrclndv u A (syn_cuni (syn_cuni (.cv p))) (syn_cuni (syn_cuni (.cv q))) dv_cache_0002
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q))))) (syn_wbr (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (.cv u)) (syn_cuni (syn_cuni (.cv q))))) p0021 p0022
  have p0024 :=
    @g_bicomd (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q))))) (syn_wbr (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) p0023
  have p0025 :=
    @g_bitrd (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q))))) p0002 p0024
  have p0026 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0027 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv r) (syn_chncodecmpset A)) p0026 p0027
  have p0029 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0030 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0029 p0030
  have p0032 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0033 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0032 p0033
  have p0035 :=
    @g_pw12argcl (.cv p) (syn_cfv (syn_c2nd) (.cv u))
  have p0036 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))))) p0034 p0035
  have p0037 :=
    @g_simpld (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))) p0036
  have p0038 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) p0031 p0037
  have p0039 :=
    @g_hnwcutcodeambientclndv u A (syn_cuni (syn_cuni (.cv p))) dv_cache_0002
  have p0040 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwcn A)) p0038 p0039
  have p0041 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0042 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0041 p0042
  have p0044 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0045 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
  have p0046 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0044 p0045
  have p0047 :=
    @g_pw12argcl (.cv q) (syn_cfv (syn_c2nd) (.cv u))
  have p0048 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0046 p0047
  have p0049 :=
    @g_simpld (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0048
  have p0050 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))) p0043 p0049
  have p0051 :=
    @g_hnwcutcodeambientclndv u A (syn_cuni (syn_cuni (.cv q))) dv_cache_0002
  have p0052 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn A)) p0050 p0051
  have p0053 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn A)) p0040 p0052
  have p0054 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn A))) p0028 p0053
  have p0055 :=
    @g_hncodecmpquotbrproxyimpclndv A (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) r dv_cache_0003 hyp_hnwcutambordbrproxyimpndv_1
  have p0056 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))))) p0054 p0055
  have p0057 :=
    @g_bicomd (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wbr (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q))))) p0056
  have p0058 :=
    @g_bitrd (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q))))) (syn_wbr (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) p0025 p0057
  have p0059 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0060 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
  have p0061 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0059 p0060
  have p0062 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0063 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0064 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0062 p0063
  have p0065 :=
    @g_hnwcutambfactorvalimpndv u A p dv_cache_0004 dv_cache_0002 dv_cache_0005 hyp_hnwcutambordbrproxyimpndv_1
  have p0066 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv u) (syn_chwcn A)) (.imp (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)))) p0064 p0065
  have p0067 :=
    @g_mpd (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A))) p0061 p0066
  have p0068 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0069 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
  have p0070 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0068 p0069
  have p0071 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0072 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0073 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0071 p0072
  have p0074 :=
    @g_hnwcutambfactorvalimpndv u A q dv_cache_0006 dv_cache_0002 dv_cache_0007 hyp_hnwcutambordbrproxyimpndv_1
  have p0075 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv u) (syn_chwcn A)) (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))) p0073 p0074
  have p0076 :=
    @g_mpd (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) p0070 p0075
  have p0077 :=
    @g_breq12d (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) p0067 p0076
  have p0078 :=
    @g_bicomd (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q))) (syn_wbr (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) p0077
  have p0079 :=
    @g_bitrd (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q))) p0058 p0078
  exact p0079

noncomputable def g_hnwcutambfactorfnnoarndv
    (A : Class) (D : Class) (R : Class) (hyp_hnwcutambfactorfnnoarndv_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnwcutambfactorfnnoarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_hnwcutambfactorfnnoarndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_hnqmap1f A hyp_hnwcutambfactorfnnoarndv_3
  have p0001 :=
    @g_hnwcutrelfndv D R hyp_hnwcutambfactorfnnoarndv_2
  have p0002 :=
    @g_hwcnssbase A D hyp_hnwcutambfactorfnnoarndv_1
  have p0003 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) (syn_wss (syn_chwcn D) (syn_chwcn A)) p0001 p0002
  have p0004 :=
    @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_chwcn A) (syn_chnwcutrel R D)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_sifmap (syn_cpw1 D) (syn_chwcn A) (syn_chnwcutrel R D)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) (syn_wf (syn_csi (syn_chnwcutrel R D)) (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_chwcn A))) p0000 p0007
  have p0009 :=
    @g_fco (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_chwcn A)) (syn_chnord A) (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))
  have p0010 :=
    Nominal.mp p0008 p0009
  exact p0010

noncomputable def g_hnwcutclassinjambnoarndv
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (hyp_hnwcutclassinjambnoarndv_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnwcutclassinjambnoarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_hnwcutclassinjambnoarndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))) (.classEq B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_simpr (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
  have p0001 :=
    @g_simpl (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
  have p0002 :=
    @g_hwcnssbase A D hyp_hnwcutclassinjambnoarndv_1
  have p0003 :=
    @g_simpl (.classMem B D) (.classMem C D)
  have p0004 :=
    @g_hnwcutcodecnclndv B D R hyp_hnwcutclassinjambnoarndv_2
  have p0005 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0003 p0004
  have p0006 :=
    @g_sseldi (syn_wa (.classMem B D) (.classMem C D)) (syn_chwcn D) (syn_chwcn A) (syn_chnwcutcode R D B) p0002 p0005
  have p0007 :=
    @g_hwcnssbase A D hyp_hnwcutclassinjambnoarndv_1
  have p0008 :=
    @g_simpr (.classMem B D) (.classMem C D)
  have p0009 :=
    @g_hnwcutcodecnclndv C D R hyp_hnwcutclassinjambnoarndv_2
  have p0010 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem C D) (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)) p0008 p0009
  have p0011 :=
    @g_sseldi (syn_wa (.classMem B D) (.classMem C D)) (syn_chwcn D) (syn_chwcn A) (syn_chnwcutcode R D C) p0007 p0010
  have p0012 :=
    @g_jca (syn_wa (.classMem B D) (.classMem C D)) (.classMem (syn_chnwcutcode R D B) (syn_chwcn A)) (.classMem (syn_chnwcutcode R D C) (syn_chwcn A)) p0006 p0011
  have p0013 :=
    @g_hwnisoclasseqbcl A (syn_chnwcutcode R D B) (syn_chnwcutcode R D C) hyp_hnwcutclassinjambnoarndv_3
  have p0014 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (syn_wa (.classMem (syn_chnwcutcode R D B) (syn_chwcn A)) (.classMem (syn_chnwcutcode R D C) (syn_chwcn A))) (syn_wb (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C))) p0012 p0013
  have p0015 :=
    @g_biimpd (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C)) p0014
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (syn_wa (.classMem B D) (.classMem C D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C))) p0001 p0015
  have p0017 :=
    @g_mpd (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C)) p0000 p0016
  have p0018 :=
    @g_simpl (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
  have p0019 :=
    @g_simpl (.classMem B D) (.classMem C D)
  have p0020 :=
    @g_hnwcutcodecnclndv B D R hyp_hnwcutclassinjambnoarndv_2
  have p0021 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0019 p0020
  have p0022 :=
    @g_simpr (.classMem B D) (.classMem C D)
  have p0023 :=
    @g_hnwcutcodecnclndv C D R hyp_hnwcutclassinjambnoarndv_2
  have p0024 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem C D) (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)) p0022 p0023
  have p0025 :=
    @g_jca (syn_wa (.classMem B D) (.classMem C D)) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)) p0021 p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (syn_wa (.classMem B D) (.classMem C D)) (syn_wa (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D C) (syn_chwcn D))) p0018 p0025
  have p0027 :=
    @g_hwnisobaserestrcl A (syn_chnwcutcode R D B) (syn_chnwcutcode R D C) D
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (syn_wa (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D C) (syn_chwcn D))) (.imp (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C)) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C))) p0026 p0027
  have p0029 :=
    @g_mpd (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C)) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C)) p0017 p0028
  have p0030 :=
    @g_simpl (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
  have p0031 :=
    @g_simpl (.classMem B D) (.classMem C D)
  have p0032 :=
    @g_hnwcutcodecnclndv B D R hyp_hnwcutclassinjambnoarndv_2
  have p0033 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0031 p0032
  have p0034 :=
    @g_simpr (.classMem B D) (.classMem C D)
  have p0035 :=
    @g_hnwcutcodecnclndv C D R hyp_hnwcutclassinjambnoarndv_2
  have p0036 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem C D) (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)) p0034 p0035
  have p0037 :=
    @g_jca (syn_wa (.classMem B D) (.classMem C D)) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)) p0033 p0036
  have p0038 :=
    @g_syl (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (syn_wa (.classMem B D) (.classMem C D)) (syn_wa (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D C) (syn_chwcn D))) p0030 p0037
  have p0039 :=
    @g_brex R D (syn_cwe)
  have p0040 :=
    Nominal.mp hyp_hnwcutclassinjambnoarndv_2 p0039
  have p0041 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0040
  have p0042 :=
    @g_hwnisoclasseqbcl D (syn_chnwcutcode R D B) (syn_chnwcutcode R D C) p0041
  have p0043 :=
    @g_syl (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (syn_wa (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D C) (syn_chwcn D))) (syn_wb (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C))) p0038 p0042
  have p0044 :=
    @g_biimprd (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C)) p0043
  have p0045 :=
    @g_mpd (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) p0029 p0044
  have p0046 :=
    @g_simpl (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
  have p0047 :=
    @g_hnwcutclassinjclndv B C D R hyp_hnwcutclassinjambnoarndv_2
  have p0048 :=
    @g_syl (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (syn_wa (.classMem B D) (.classMem C D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)) p0046 p0047
  have p0049 :=
    @g_mpd (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C) p0045 p0048
  have p0050 :=
    @g_ex (syn_wa (.classMem B D) (.classMem C D)) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))) (.classEq B C) p0049
  exact p0050

#print axioms g_hnwcutclassinjambnoarndv

end NFChoice.DirectNominalPrf.WPPReplay
