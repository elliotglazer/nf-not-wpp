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
import NominalWPPReplayChunk017Compact001Part004

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

noncomputable def g_hnsicodemapf1ndv
    (A : Class) :
    Nominal.NPrf (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (h)
  have fresh_q_ne_r : q ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_q, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_chnsicodemap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_chnsicodemap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have p0000 :=
    @g_hnsicodemapfndv A
  have p0001 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0002 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0003 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0001 p0002
  have p0004 :=
    @g_hnwpw1argcl (syn_chwcn A) q
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0003 p0004
  have p0006 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0007 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005 p0006
  have p0008 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0009 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0010 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0008 p0009
  have p0011 :=
    @g_hnwpw1argcl (syn_chwcn A) q
  have p0012 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0010 p0011
  have p0013 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0014 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) p0012 p0013
  have p0015 :=
    @g_hwcnpairclndv A (syn_cuni (.cv q))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0014 p0015
  have p0017 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0018 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0019 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0017 p0018
  have p0020 :=
    @g_hnsicodemapvalndv A q dv_cache_0001
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) p0019 p0020
  have p0022 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0021
  have p0023 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0024 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0025 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0024 p0025
  have p0027 :=
    @g_hnsicodemapvalndv A r dv_cache_0002
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0026 p0027
  have p0029 :=
    @g_n_3eqtrd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) p0022 p0023 p0028
  have p0030 :=
    @g_opth (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))
  have p0031 :=
    @g_biimpi (.classEq (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0030
  have p0032 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classEq (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0029 p0031
  have p0033 :=
    @g_simpl (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) p0032 p0033
  have p0035 :=
    @g_siinjndv (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv r))) p0034
  have p0036 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0037 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0038 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0036 p0037
  have p0039 :=
    @g_hnsicodemapvalndv A q dv_cache_0001
  have p0040 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) p0038 p0039
  have p0041 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0040
  have p0042 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0043 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0044 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0045 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0043 p0044
  have p0046 :=
    @g_hnsicodemapvalndv A r dv_cache_0002
  have p0047 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0045 p0046
  have p0048 :=
    @g_n_3eqtrd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) p0041 p0042 p0047
  have p0049 :=
    @g_opth (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))
  have p0050 :=
    @g_biimpi (.classEq (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0049
  have p0051 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classEq (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) p0048 p0050
  have p0052 :=
    @g_simpr (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
  have p0053 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) p0051 p0052
  have p0054 :=
    @g_pw111 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))
  have p0055 :=
    @g_biimpi (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) (.classEq (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) p0054
  have p0056 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) (.classEq (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) p0053 p0055
  have p0057 :=
    @g_opeq12d (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r))) p0035 p0056
  have p0058 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0059 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0060 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0058 p0059
  have p0061 :=
    @g_hnwpw1argcl (syn_chwcn A) r
  have p0062 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) p0060 p0061
  have p0063 :=
    @g_simpl (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0064 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0062 p0063
  have p0065 :=
    @g_hwcnpairclndv A (syn_cuni (.cv r))
  have p0066 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (syn_cuni (.cv r)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) p0064 p0065
  have p0067 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_cuni (.cv r)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) p0066
  have p0068 :=
    @g_n_3eqtrd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) (syn_cuni (.cv r)) p0016 p0057 p0067
  have p0069 :=
    @g_sneqd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_cuni (.cv q)) (syn_cuni (.cv r)) p0068
  have p0070 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0071 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0072 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0070 p0071
  have p0073 :=
    @g_hnwpw1argcl (syn_chwcn A) r
  have p0074 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) p0072 p0073
  have p0075 :=
    @g_simpr (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0076 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))) p0074 p0075
  have p0077 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.cv r) (syn_csn (syn_cuni (.cv r))) p0076
  have p0078 :=
    @g_n_3eqtrd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_cuni (.cv r))) (.cv r) p0007 p0069 p0077
  have p0079 :=
    @g_ex (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r)) p0078
  have p0080 :=
    @g_ex (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.imp (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))) p0079
  have p0081 :=
    @g_ralrimiv (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.imp (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))) r (syn_cpw1 (syn_chwcn A)) dv_cache_0003 p0080
  have p0082 :=
    @g_rgen (syn_wral r (syn_cpw1 (syn_chwcn A)) (.imp (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r)))) q (syn_cpw1 (syn_chwcn A)) p0081
  have p0083 :=
    @g_pm3_2i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wral q (syn_cpw1 (syn_chwcn A)) (syn_wral r (syn_cpw1 (syn_chwcn A)) (.imp (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))))) p0000 p0082
  have p0084 :=
    @g_dff13 q r (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_chnsicodemap A) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0085_e00_recanon : Nominal.NPrf (syn_wb (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wral q (syn_cpw1 (syn_chwcn A)) (syn_wral r (syn_cpw1 (syn_chwcn A)) (.imp (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_chnsicodemap syn_cres syn_chnsicodeliftfn syn_ctxp syn_clnpwsirelfn syn_clnpwpw1secondfn syn_cpw1 syn_chwcn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
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
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
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
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0084
  have p0085 :=
    @g_biimpri (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wral q (syn_cpw1 (syn_chwcn A)) (syn_wral r (syn_cpw1 (syn_chwcn A)) (.imp (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (.cv q) (.cv r)))))) p0085_e00_recanon
  have p0086 :=
    Nominal.mp p0083 p0085
  exact p0086

noncomputable def g_hnsicodemapf1ondv
    (A : Class) :
    Nominal.NPrf (syn_wf1o (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hnsicodemapf1ndv A
  have p0001 :=
    @g_hnsicodemapfondv A
  have p0002 :=
    @g_pm3_2i (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))))
  have p0004 :=
    @g_biimpri (syn_wf1o (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (syn_wf1 (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))) p0003
  have p0005 :=
    Nominal.mp p0002 p0004
  exact p0005

noncomputable def g_hnsiquomapexgndv
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chnsiquomap A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chnsiquomap] using (Nominal.classEqRefl (syn_chnsiquomap A)))
  have p0001 :=
    @g_a1i (.classEq (syn_chnsiquomap A) (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A)))) (.classMem A (syn_cvv)) p0000
  have p0002 :=
    @g_hnsicodemapexgndv A
  have p0003 :=
    @g_imageexg (syn_chnsicodemap A) (syn_cvv)
  have p0004 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chnsicodemap A) (syn_cvv)) (.classMem (syn_cimage (syn_chnsicodemap A)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_pw1fnex
  have p0006 :=
    @g_a1i (.classMem (syn_cpw1fn) (syn_cvv)) (.classMem A (syn_cvv)) p0005
  have p0007 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cimage (syn_chnsicodemap A)) (syn_cvv)) (.classMem (syn_cpw1fn) (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_coexg (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_cimage (syn_chnsicodemap A)) (syn_cvv)) (.classMem (syn_cpw1fn) (syn_cvv))) (.classMem (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_hnordexg A
  have p0011 :=
    @g_pw1exg (syn_chnord A) (syn_cvv)
  have p0012 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chnord A) (syn_cvv)) (.classMem (syn_cpw1 (syn_chnord A)) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cvv)) (.classMem (syn_cpw1 (syn_chnord A)) (syn_cvv)) p0009 p0012
  have p0014 :=
    @g_resexg (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A)) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cvv)) (.classMem (syn_cpw1 (syn_chnord A)) (syn_cvv))) (.classMem (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A))) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_eqeltrd (.classMem A (syn_cvv)) (syn_chnsiquomap A) (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A))) (syn_cvv) p0001 p0015
  exact p0016

noncomputable def g_hnsiquomapfnndv
    (A : Class) (hyp_hnsiquomapfnndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hnsicodemapexgndv A
  have p0001 :=
    Nominal.mp hyp_hnsiquomapfnndv_1 p0000
  have p0002 :=
    @g_wppimagefn (syn_chnsicodemap A) p0001
  have p0003 :=
    @g_fnpw1fn
  have p0004 :=
    @g_ssv (syn_crn (syn_cpw1fn))
  have p0005 :=
    @g_n_3pm3_2i (syn_wfn (syn_cimage (syn_chnsicodemap A)) (syn_cvv)) (syn_wfn (syn_cpw1fn) (syn_c1c)) (syn_wss (syn_crn (syn_cpw1fn)) (syn_cvv)) p0002 p0003 p0004
  have p0006 :=
    @g_fnco (syn_cvv) (syn_c1c) (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pw1ss1c (syn_chnord A)
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_c1c)) (syn_wss (syn_cpw1 (syn_chnord A)) (syn_c1c)) p0007 p0008
  have p0010 :=
    @g_fnssres (syn_c1c) (syn_cpw1 (syn_chnord A)) (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    (by simpa [syn_chnsiquomap] using (Nominal.classEqRefl (syn_chnsiquomap A)))
  have p0013 :=
    @g_fneq1i (syn_cpw1 (syn_chnord A)) (syn_chnsiquomap A) (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A))) p0012
  have p0014 :=
    @g_mpbir (syn_wfn (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A))) (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A))) (syn_cpw1 (syn_chnord A))) p0011 p0013
  exact p0014

noncomputable def g_hnsiquomapvalndv
    (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) (hyp_hnsiquomapvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))))) := by
  let proofSupport : Finset Var := A.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : Disjoint ((syn_cpw1 (syn_cuni (.cv q)))).fv ((syn_chnsicodemap A)).fv := by
    exact (show Disjoint ((syn_cpw1 (syn_cuni (.cv q)))).fv ((syn_chnsicodemap A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap]; exact (show Disjoint (((syn_cuni (.cv q))).fv) ((A).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv q)).fv) ((A).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) ((A).fv) from (Finset.disjoint_singleton_left.mpr (show q ∉ (A).fv from (by exact dv_A_q))))))))))
  have p0000 :=
    (by simpa [syn_chnsiquomap] using (Nominal.classEqRefl (syn_chnsiquomap A)))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_chnsiquomap A) (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A))) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A))) (.cv q))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0001
  have p0003 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_chnord A)) (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn))
  have p0004 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A))) (.cv q)) (syn_cfv (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (.cv q)) p0002 p0003
  have p0005 :=
    @g_fnpw1fn
  have p0006 :=
    @g_a1i (syn_wfn (syn_cpw1fn) (syn_c1c)) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0005
  have p0007 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
  have p0008 :=
    @g_pw1ss1c (syn_chnord A)
  have p0009 :=
    @g_sseli (syn_cpw1 (syn_chnord A)) (syn_c1c) (.cv q) p0008
  have p0010 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv q) (syn_c1c)) p0007 p0009
  have p0011 :=
    @g_jca (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wfn (syn_cpw1fn) (syn_c1c)) (.classMem (.cv q) (syn_c1c)) p0006 p0010
  have p0012 :=
    @g_fvco2 (syn_c1c) (.cv q) (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)
  have p0013 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (syn_wfn (syn_cpw1fn) (syn_c1c)) (.classMem (.cv q) (syn_c1c))) (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (.cv q)) (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cfv (syn_cpw1fn) (.cv q)))) p0011 p0012
  have p0014 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (.cv q)) (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cfv (syn_cpw1fn) (.cv q))) p0004 p0013
  have p0015 :=
    @g_hnwpw1argcl (syn_chnord A) q
  have p0016 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0015
  have p0017 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_cpw1fn) p0016
  have p0018 :=
    @g_vex q
  have p0019 :=
    @g_uniex (.cv q) p0018
  have p0020 :=
    @g_pw1fnval (syn_cuni (.cv q)) p0019
  have p0021 :=
    @g_a1i (.classEq (syn_cfv (syn_cpw1fn) (syn_csn (syn_cuni (.cv q)))) (syn_cpw1 (syn_cuni (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0020
  have p0022 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_cfv (syn_cpw1fn) (.cv q)) (syn_cfv (syn_cpw1fn) (syn_csn (syn_cuni (.cv q)))) (syn_cpw1 (syn_cuni (.cv q))) p0017 p0021
  have p0023 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_cfv (syn_cpw1fn) (.cv q)) (syn_cpw1 (syn_cuni (.cv q))) (syn_cimage (syn_chnsicodemap A)) p0022
  have p0024 :=
    @g_hnsicodemapexgndv A
  have p0025 :=
    Nominal.mp hyp_hnsiquomapvalndv_1 p0024
  have p0026 :=
    @g_vex q
  have p0027 :=
    @g_uniex (.cv q) p0026
  have p0028 :=
    @g_pw1ex (syn_cuni (.cv q)) p0027
  have p0029 :=
    @g_wppfvimage (syn_cpw1 (syn_cuni (.cv q))) (syn_chnsicodemap A) dv_cache_0001 p0025 p0028
  have p0030 :=
    @g_a1i (.classEq (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cpw1 (syn_cuni (.cv q)))) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q))))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0029
  have p0031 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cfv (syn_cpw1fn) (.cv q))) (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cpw1 (syn_cuni (.cv q)))) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))) p0023 p0030
  have p0032 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_cimage (syn_chnsicodemap A)) (syn_cfv (syn_cpw1fn) (.cv q))) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))) p0014 p0031
  exact p0032

#print axioms g_hnsiquomapvalndv

end NFChoice.DirectNominalPrf.WPPReplay
