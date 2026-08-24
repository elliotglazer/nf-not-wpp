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
import NominalWPPReplayChunk016Compact001Part051

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

noncomputable def g_pwpullssxpsetimpndv
    (x : Var) (y : Var) (f : Var) (r : Var) (dv_f_r : f ≠ r) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y) (dv_r_x : r ≠ x) (dv_r_y : r ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({f} : Finset Var) ∪ ({r} : Finset Var)
  have p0000 :=
    @g_ssdmrn (syn_cpwpull (.cv f) (.cv r))
  have p0001 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r))))
  have p0002 :=
    @g_dmeqi (syn_cpwpull (.cv f) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0001
  have p0003 :=
    @g_dmcoss (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)
  have p0004 :=
    @g_eqsstri (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (syn_cdm (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f))) (syn_cdm (.cv f)) p0002 p0003
  have p0005 :=
    @g_fofn (.cv x) (.cv y) (.cv f)
  have p0006 :=
    @g_id (syn_wfo (.cv f) (.cv x) (.cv y))
  have p0007 :=
    @g_a1ii (.imp (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfn (.cv f) (.cv x))) (.imp (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfo (.cv f) (.cv x) (.cv y))) p0005 p0006
  have p0008 :=
    @g_fndm (.cv x) (.cv f)
  have p0009 :=
    @g_syl (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfn (.cv f) (.cv x)) (.classEq (syn_cdm (.cv f)) (.cv x)) p0007 p0008
  have p0010 :=
    @g_syl5sseq (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_cdm (.cv f)) (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (.cv x) p0004 p0009
  have p0011 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r))))
  have p0012 :=
    @g_rneqi (syn_cpwpull (.cv f) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0011
  have p0013 :=
    @g_rncoss (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)
  have p0014 :=
    @g_eqsstri (syn_crn (syn_cpwpull (.cv f) (.cv r))) (syn_crn (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f))) (syn_crn (syn_ccom (syn_ccnv (.cv f)) (.cv r))) p0012 p0013
  have p0015 :=
    @g_rncoss (syn_ccnv (.cv f)) (.cv r)
  have p0016 :=
    @g_sstri (syn_crn (syn_cpwpull (.cv f) (.cv r))) (syn_crn (syn_ccom (syn_ccnv (.cv f)) (.cv r))) (syn_crn (syn_ccnv (.cv f))) p0014 p0015
  have p0017 :=
    @g_dfrn4 (syn_ccnv (.cv f))
  have p0018 :=
    @g_cnvcnv (.cv f)
  have p0019 :=
    @g_dmeqi (syn_ccnv (syn_ccnv (.cv f))) (.cv f) p0018
  have p0020 :=
    @g_eqtri (syn_crn (syn_ccnv (.cv f))) (syn_cdm (syn_ccnv (syn_ccnv (.cv f)))) (syn_cdm (.cv f)) p0017 p0019
  have p0021 :=
    @g_sseqtri (syn_crn (syn_cpwpull (.cv f) (.cv r))) (syn_crn (syn_ccnv (.cv f))) (syn_cdm (.cv f)) p0016 p0020
  have p0022 :=
    @g_syl5sseq (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_cdm (.cv f)) (syn_crn (syn_cpwpull (.cv f) (.cv r))) (.cv x) p0021 p0009
  have p0023 :=
    @g_jca (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wss (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (.cv x)) (syn_wss (syn_crn (syn_cpwpull (.cv f) (.cv r))) (.cv x)) p0010 p0022
  have p0024 :=
    @g_xpss12 (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (.cv x) (syn_crn (syn_cpwpull (.cv f) (.cv r))) (.cv x)
  have p0025 :=
    @g_syl (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wa (syn_wss (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (.cv x)) (syn_wss (syn_crn (syn_cpwpull (.cv f) (.cv r))) (.cv x))) (syn_wss (syn_cxp (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (syn_crn (syn_cpwpull (.cv f) (.cv r)))) (syn_cxp (.cv x) (.cv x))) p0023 p0024
  have p0026 :=
    @g_syl5ss (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (syn_crn (syn_cpwpull (.cv f) (.cv r)))) (syn_cxp (.cv x) (.cv x)) p0000 p0025
  exact p0026

noncomputable def g_elhwcodesclndv
    (B : Class) (C : Class) (D : Class) (hyp_elhwcodesclndv_1 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_elhwcodesclndv_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop B C) (syn_chwcodes D)) (syn_wa (syn_wbr B (syn_cwe) C) (syn_wss C D))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (D).fv ((Class.cv r)).fv := by
    exact (show Disjoint (D).fv ((Class.cv r)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((D).fv) (({r} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show r ∉ (D).fv from (by exact fresh_r_not_D))))))
  have dv_cache_0002 : r ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((syn_wb (.classMem (syn_cop B C) (syn_chwcodes D)) (syn_wa (syn_wbr B (syn_cwe) C) (syn_wss C D)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_B, fresh_r_not_C, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv r) B)
  have p0001 :=
    @g_opeq1d (.classEq (.cv r) B) (.cv r) B C p0000
  have p0002 :=
    @g_eleq1d (.classEq (.cv r) B) (syn_cop (.cv r) C) (syn_cop B C) (syn_chwcodes D) p0001
  have p0003 :=
    @g_id (.classEq (.cv r) B)
  have p0004 :=
    @g_breq1d (.classEq (.cv r) B) (.cv r) B C (syn_cwe) p0003
  have p0005 :=
    @g_biid (syn_wss C D)
  have p0006 :=
    @g_a1i (syn_wb (syn_wss C D) (syn_wss C D)) (.classEq (.cv r) B) p0005
  have p0007 :=
    @g_anbi12d (.classEq (.cv r) B) (syn_wbr (.cv r) (syn_cwe) C) (syn_wbr B (syn_cwe) C) (syn_wss C D) (syn_wss C D) p0004 p0006
  have p0008 :=
    @g_bibi12d (.classEq (.cv r) B) (.classMem (syn_cop (.cv r) C) (syn_chwcodes D)) (.classMem (syn_cop B C) (syn_chwcodes D)) (syn_wa (syn_wbr (.cv r) (syn_cwe) C) (syn_wss C D)) (syn_wa (syn_wbr B (syn_cwe) C) (syn_wss C D)) p0002 p0007
  have p0009 :=
    @g_vex r
  have p0010 :=
    @g_elhwcodes D C (.cv r) dv_cache_0001 p0009 hyp_elhwcodesclndv_2
  have p0011 :=
    @g_vtocl (syn_wb (.classMem (syn_cop (.cv r) C) (syn_chwcodes D)) (syn_wa (syn_wbr (.cv r) (syn_cwe) C) (syn_wss C D))) (syn_wb (.classMem (syn_cop B C) (syn_chwcodes D)) (syn_wa (syn_wbr B (syn_cwe) C) (syn_wss C D))) r B dv_cache_0002 dv_cache_0003 hyp_elhwcodesclndv_1 p0008 p0010
  exact p0011

noncomputable def g_hwbijf1oclndv
    (B : Class) (hyp_hwbijf1oclndv_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem B (syn_chwbij)) (syn_wf1o B (syn_cdm B) (syn_crn B))) := by
  let proofSupport : Finset Var := B.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (h)
  have dv_cache_0001 : f ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((syn_wb (.classMem B (syn_chwbij)) (syn_wf1o B (syn_cdm B) (syn_crn B)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv f) B)
  have p0001 :=
    @g_eleq1d (.classEq (.cv f) B) (.cv f) B (syn_chwbij) p0000
  have p0002 :=
    @g_f1oeq1 (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv f) B
  have p0003 :=
    @g_id (.classEq (.cv f) B)
  have p0004 :=
    @g_dmeqd (.classEq (.cv f) B) (.cv f) B p0003
  have p0005 :=
    @g_id (.classEq (.cv f) B)
  have p0006 :=
    @g_rneqd (.classEq (.cv f) B) (.cv f) B p0005
  have p0007 :=
    @g_jca (.classEq (.cv f) B) (.classEq (syn_cdm (.cv f)) (syn_cdm B)) (.classEq (syn_crn (.cv f)) (syn_crn B)) p0004 p0006
  have p0008 :=
    @g_f1oeq23 (syn_cdm (.cv f)) (syn_cdm B) (syn_crn (.cv f)) (syn_crn B) B
  have p0009 :=
    @g_syl (.classEq (.cv f) B) (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cdm B)) (.classEq (syn_crn (.cv f)) (syn_crn B))) (syn_wb (syn_wf1o B (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wf1o B (syn_cdm B) (syn_crn B))) p0007 p0008
  have p0010 :=
    @g_bitrd (.classEq (.cv f) B) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wf1o B (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wf1o B (syn_cdm B) (syn_crn B)) p0002 p0009
  have p0011 :=
    @g_bibi12d (.classEq (.cv f) B) (.classMem (.cv f) (syn_chwbij)) (.classMem B (syn_chwbij)) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wf1o B (syn_cdm B) (syn_crn B)) p0001 p0010
  have p0012 :=
    @g_hwbijf1o f
  have p0013 :=
    @g_vtoclg (syn_wb (.classMem (.cv f) (syn_chwbij)) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))) (syn_wb (.classMem B (syn_chwbij)) (syn_wf1o B (syn_cdm B) (syn_crn B))) f B (syn_cvv) dv_cache_0001 dv_cache_0002 p0011 p0012
  have p0014 :=
    Nominal.mp hyp_hwbijf1oclndv_1 p0013
  exact p0014

#print axioms g_hwbijf1oclndv

end NFChoice.DirectNominalPrf.WPPReplay
