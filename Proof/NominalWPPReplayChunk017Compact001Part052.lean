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
import NominalWPPReplayChunk017Compact001Part051

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

noncomputable def g_wppconcrete6dmrepdndv
    (x : Var) (z : Var) (dv_x_z : x ≠ z) :
    Nominal.NPrf (.imp (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (syn_wex z (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({z} : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_z : q ≠ z := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_q : z ≠ q :=
    Ne.symm fresh_q_ne_z
  have dv_cache_0001 : q ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cwppcardt6fn)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_q, (Ne.symm dv_x_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_wex z (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppconcrete6fndmndv
  have p0001 :=
    @g_eleq2i (syn_cdm (syn_cwppconcrete6fn)) (syn_crn (syn_cwppcardt6fn)) (.cv x) p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn))) p0001
  have p0003 :=
    @g_wppcardt6fnmapndv
  have p0004 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_fvelrnb q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.cv x) (syn_cwppcardt6fn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_biimpi (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn))) (syn_wrex q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) p0007
  have p0009 :=
    @g_syl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn))) (syn_wrex q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) p0002 p0008
  have p0010 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))
  have p0011 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
  have p0012 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.cv q)
  have p0013 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0011 p0012
  have p0014 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0015 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0013 p0014
  have p0016 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cuni (.cv q))
  have p0017 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0015 p0016
  have p0018 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
  have p0019 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0017 p0018
  have p0020 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cuni (syn_cuni (.cv q)))
  have p0021 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) p0019 p0020
  have p0022 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0023 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0021 p0022
  have p0024 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cuni (syn_cuni (syn_cuni (.cv q))))
  have p0025 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) p0023 p0024
  have p0026 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
  have p0027 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0025 p0026
  have p0028 :=
    @g_pw1argclcl (syn_cpw1 (syn_cncs)) (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
  have p0029 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) p0027 p0028
  have p0030 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
  have p0031 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) p0029 p0030
  have p0032 :=
    @g_pw1argclcl (syn_cncs) (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0033 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) p0031 p0032
  have p0034 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
  have p0035 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) p0033 p0034
  have p0036 :=
    @g_elncs z (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) dv_cache_0004
  have p0037 :=
    @g_biimpi (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (syn_wex z (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) p0036
  have p0038 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (syn_wex z (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) p0035 p0037
  have p0039 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wex z (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) p0010 p0038
  have p0040 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))
  have p0041 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))
  have p0042 :=
    @g_eqcomd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x) p0041
  have p0043 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))
  have p0044 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
  have p0045 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.cv q)
  have p0046 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0044 p0045
  have p0047 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0048 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0046 p0047
  have p0049 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
  have p0050 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.cv q)
  have p0051 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0049 p0050
  have p0052 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0053 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0051 p0052
  have p0054 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cuni (.cv q))
  have p0055 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0053 p0054
  have p0056 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
  have p0057 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q))))) p0055 p0056
  have p0058 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
  have p0059 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.cv q)
  have p0060 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0058 p0059
  have p0061 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0062 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0060 p0061
  have p0063 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cuni (.cv q))
  have p0064 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0062 p0063
  have p0065 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
  have p0066 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0064 p0065
  have p0067 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cuni (syn_cuni (.cv q)))
  have p0068 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) p0066 p0067
  have p0069 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0070 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) p0068 p0069
  have p0071 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
  have p0072 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.cv q)
  have p0073 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0071 p0072
  have p0074 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0075 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0073 p0074
  have p0076 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cuni (.cv q))
  have p0077 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0075 p0076
  have p0078 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
  have p0079 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0077 p0078
  have p0080 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cuni (syn_cuni (.cv q)))
  have p0081 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) p0079 p0080
  have p0082 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0083 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0081 p0082
  have p0084 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cuni (syn_cuni (syn_cuni (.cv q))))
  have p0085 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) p0083 p0084
  have p0086 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
  have p0087 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) p0085 p0086
  have p0088 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
  have p0089 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.cv q)
  have p0090 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0088 p0089
  have p0091 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0092 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0090 p0091
  have p0093 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cuni (.cv q))
  have p0094 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0092 p0093
  have p0095 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
  have p0096 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0094 p0095
  have p0097 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cuni (syn_cuni (.cv q)))
  have p0098 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) p0096 p0097
  have p0099 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0100 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0098 p0099
  have p0101 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cuni (syn_cuni (syn_cuni (.cv q))))
  have p0102 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) p0100 p0101
  have p0103 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
  have p0104 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0102 p0103
  have p0105 :=
    @g_pw1argclcl (syn_cpw1 (syn_cncs)) (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
  have p0106 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) p0104 p0105
  have p0107 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
  have p0108 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) p0106 p0107
  have p0109 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
  have p0110 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.cv q)
  have p0111 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0109 p0110
  have p0112 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0113 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0111 p0112
  have p0114 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cuni (.cv q))
  have p0115 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0113 p0114
  have p0116 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
  have p0117 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0115 p0116
  have p0118 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cuni (syn_cuni (.cv q)))
  have p0119 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) p0117 p0118
  have p0120 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0121 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0119 p0120
  have p0122 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cuni (syn_cuni (syn_cuni (.cv q))))
  have p0123 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) p0121 p0122
  have p0124 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
  have p0125 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0123 p0124
  have p0126 :=
    @g_pw1argclcl (syn_cpw1 (syn_cncs)) (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
  have p0127 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) p0125 p0126
  have p0128 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
  have p0129 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) p0127 p0128
  have p0130 :=
    @g_pw1argclcl (syn_cncs) (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0131 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) p0129 p0130
  have p0132 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
  have p0133 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) p0131 p0132
  have p0134 :=
    @g_sneq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
  have p0135 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) (.classEq (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) p0133 p0134
  have p0136 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) p0108 p0135
  have p0137 :=
    @g_sneq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
  have p0138 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) (.classEq (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))) p0136 p0137
  have p0139 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) p0087 p0138
  have p0140 :=
    @g_sneq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))
  have p0141 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))) (.classEq (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))) p0139 p0140
  have p0142 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))) p0070 p0141
  have p0143 :=
    @g_sneq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))
  have p0144 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))) (.classEq (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))) p0142 p0143
  have p0145 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))) p0057 p0144
  have p0146 :=
    @g_sneq (syn_cuni (.cv q)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))
  have p0147 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))) (.classEq (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))) p0145 p0146
  have p0148 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))) p0048 p0147
  have p0149 :=
    @g_fveq2 (.cv q) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))) (syn_cwppcardt6fn)
  have p0150 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (.cv q) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))))) p0148 p0149
  have p0151 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))
  have p0152 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.cv q)
  have p0153 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0151 p0152
  have p0154 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0155 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0153 p0154
  have p0156 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cuni (.cv q))
  have p0157 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (.cv q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0155 p0156
  have p0158 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
  have p0159 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cuni (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0157 p0158
  have p0160 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cuni (syn_cuni (.cv q)))
  have p0161 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) p0159 p0160
  have p0162 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0163 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0161 p0162
  have p0164 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cuni (syn_cuni (syn_cuni (.cv q))))
  have p0165 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) p0163 p0164
  have p0166 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
  have p0167 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0165 p0166
  have p0168 :=
    @g_pw1argclcl (syn_cpw1 (syn_cncs)) (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))
  have p0169 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) p0167 p0168
  have p0170 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))
  have p0171 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) p0169 p0170
  have p0172 :=
    @g_pw1argclcl (syn_cncs) (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))
  have p0173 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cncs))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) p0171 p0172
  have p0174 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))
  have p0175 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) p0173 p0174
  have p0176 :=
    @g_wppcardt6fnvalsingndv (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))
  have p0177 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))) p0175 p0176
  have p0178 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_cfv (syn_cwppcardt6fn) (.cv q)) (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))) p0150 p0177
  have p0179 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))) p0043 p0178
  have p0180 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.cv x) (syn_cfv (syn_cwppcardt6fn) (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))) p0042 p0179
  have p0181 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))))) p0040 p0180
  have p0182 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))
  have p0183 :=
    @g_tceq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z))
  have p0184 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z))) (.classEq (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) (syn_ctc (syn_cnc (.cv z)))) p0182 p0183
  have p0185 :=
    @g_tceq (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) (syn_ctc (syn_cnc (.cv z)))
  have p0186 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))) (syn_ctc (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) (syn_ctc (syn_ctc (syn_cnc (.cv z))))) p0184 p0185
  have p0187 :=
    @g_tceq (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) (syn_ctc (syn_ctc (syn_cnc (.cv z))))
  have p0188 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))) (syn_ctc (syn_ctc (syn_cnc (.cv z))))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))) p0186 p0187
  have p0189 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))
  have p0190 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))) p0188 p0189
  have p0191 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))
  have p0192 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) p0190 p0191
  have p0193 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))
  have p0194 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q)))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) p0192 p0193
  have p0195 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) p0181 p0194
  have p0196 :=
    @g_ex (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z))) (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) p0195
  have p0197 :=
    @g_eximdv (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z))) (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) z dv_cache_0005 p0196
  have p0198 :=
    @g_mpd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (syn_wex z (.classEq (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (.cv z)))) (syn_wex z (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0039 p0197
  have p0199 :=
    @g_ex (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)) (syn_wex z (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0198
  have p0200 :=
    @g_rexlimiv (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x)) (syn_wex z (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) dv_cache_0006 p0199
  have p0201 :=
    @g_syl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (syn_wrex q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (syn_cfv (syn_cwppcardt6fn) (.cv q)) (.cv x))) (syn_wex z (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0009 p0200
  exact p0201

#print axioms g_wppconcrete6dmrepdndv

end NFChoice.DirectNominalPrf.WPPReplay
