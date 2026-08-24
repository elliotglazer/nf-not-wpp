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
import NominalWPPReplayChunk016Compact001Part038

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

noncomputable def g_wecomparisoncutreptypedliftdndv
    (x : Var) (D : Class) (R : Class) (E : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_q : q ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_R_q : q ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_q_x : q ≠ x) :
    Nominal.NPrf (.imp (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ E.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ ((syn_csn (syn_csn (.cv x)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_q_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_q, dv_D_q, dv_R_q, dv_q_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, dv_E_x, dv_R_x, (Ne.symm dv_q_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv x) D) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0001 :=
    @g_snelpw1 (syn_csn (.cv x)) (syn_cpw1 D)
  have p0002 :=
    @g_snelpw1 (.cv x) D
  have p0003 :=
    @g_bitri (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0001 p0002
  have p0004 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv x) D) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem (.cv x) D) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classMem (.cv x) D) (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D))) p0000 p0004
  have p0006 :=
    @g_simpr (.classMem (.cv x) D) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0007 :=
    @g_jca (syn_wa (.classMem (.cv x) D) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0005 p0006
  have p0008 :=
    @g_id (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0009 :=
    @g_unieqd (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (.cv q) (syn_csn (syn_csn (.cv x))) p0008
  have p0010 :=
    @g_unieqd (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_cuni (.cv q)) (syn_cuni (syn_csn (syn_csn (.cv x)))) p0009
  have p0011 :=
    @g_snex (.cv x)
  have p0012 :=
    @g_unisn (syn_csn (.cv x)) p0011
  have p0013 :=
    @g_unieqi (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x)) p0012
  have p0014 :=
    @g_vex x
  have p0015 :=
    @g_unisn (.cv x) p0014
  have p0016 :=
    @g_eqtri (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x))))) (syn_cuni (syn_csn (.cv x))) (.cv x) p0013 p0015
  have p0017 :=
    @g_a1i (.classEq (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x))))) (.cv x)) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) p0016
  have p0018 :=
    @g_eqtrd (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x))))) (.cv x) p0010 p0017
  have p0019 :=
    @g_sneqd (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_cuni (syn_cuni (.cv q))) (.cv x) p0018
  have p0020 :=
    @g_imaeq2d (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (.cv x)) (syn_ccnv (syn_cdif R (syn_cid))) p0019
  have p0021 :=
    @g_ineq2d (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) D p0020
  have p0022 :=
    @g_nceqd (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0021
  have p0023 :=
    @g_eqeq2d (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cnc E) p0022
  have p0024 :=
    @g_rspcev (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) q (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0023
  have p0025 :=
    @g_syl (syn_wa (.classMem (.cv x) D) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wa (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) p0007 p0024
  have p0026 :=
    @g_rexlimiva (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) x D dv_cache_0004 p0025
  have p0027 :=
    @g_id (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0028 :=
    @g_a1ii (.imp (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))) (.imp (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0026 p0027
  exact p0028

noncomputable def g_wecomparisoncutreptypedtargetdfdv
    (D : Class) (R : Class) (S : Class) (E : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_E_q : q ∉ E.fv) (dv_R_q : q ∉ R.fv) (hyp_wecomparisoncutreptypedtargetdfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ ({q} : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_q : x ≠ q := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have dv_cache_0001 : x ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (E).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have p0000 :=
    @g_wecomparisoncutreplttargetdfdv x D R S E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_wecomparisoncutreptypedtargetdfdv_1
  have p0001 :=
    @g_wecomparisoncutreptypedliftdndv x D R E q dv_cache_0005 dv_cache_0001 dv_cache_0006 dv_cache_0002 dv_cache_0007 dv_cache_0003 dv_cache_0008
  have p0002 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) p0000 p0001
  exact p0002

noncomputable def g_wppcandstrictslicecutrepfixdrfdv
    (C : Class) (D : Class) (R : Class) (k : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv) (dv_C_q : q ∉ C.fv) (dv_D_k : k ∉ D.fv) (dv_D_q : q ∉ D.fv) (dv_F_k : k ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_R_k : k ∉ R.fv) (dv_R_q : q ∉ R.fv) (dv_k_q : k ≠ q) (hyp_wppcandstrictslicecutrepfixdrfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wppcandstrictslicecutrepfixdrfdv_2 : Nominal.NPrf (.classEq C (syn_cnc D))) :
    Nominal.NPrf (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ R.fv ∪ ({k} : Finset Var) ∪ F.fv ∪ ({q} : Finset Var)
  let s : Var := freshVar proofSupport 0
  let e : Var := freshVar proofSupport 1
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_s_ne_k : s ≠ k := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_k_ne_s : k ≠ s :=
    Ne.symm fresh_s_ne_k
  have fresh_s_not_F : s ∉ F.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_ne_q : s ≠ q := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_s : q ≠ s :=
    Ne.symm fresh_s_ne_q
  have fresh_e : e ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_e_not_D : e ∉ D.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_e_not_R : e ∉ R.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_e_ne_k : e ≠ k := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_k_ne_e : k ≠ e :=
    Ne.symm fresh_e_ne_k
  have fresh_e_not_F : e ∉ F.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e_ne_q : e ≠ q := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_e : q ≠ e :=
    Ne.symm fresh_e_ne_q
  have fresh_s_ne_e : s ≠ e := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_e_ne_s : e ≠ s :=
    Ne.symm fresh_s_ne_e
  have dv_cache_0001 : e ≠ k := by
    exact (show e ≠ k from (by exact fresh_e_ne_k))
  have dv_cache_0002 : e ≠ s := by
    clear dv_cache_0001
    exact (show e ≠ s from (by exact fresh_e_ne_s))
  have dv_cache_0003 : k ≠ s := by
    clear dv_cache_0001 dv_cache_0002
    exact (show k ≠ s from (by exact fresh_k_ne_s))
  have dv_cache_0004 : q ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((Class.cv e)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_q), dv_C_q, dv_F_q, fresh_q_ne_s, fresh_q_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : e ∉ ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_D, fresh_e_ne_k, fresh_e_not_R, fresh_e_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : s ∉ ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_D, fresh_s_ne_k, fresh_s_not_R, fresh_s_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : e ∉ ((Wff.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_k, fresh_e_not_C, fresh_e_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : s ∉ ((Wff.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_k, fresh_s_not_C, fresh_s_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elwppcandstrictslice C k F
  have p0001 :=
    @g_biimpi (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C)) p0000
  have p0002 :=
    @g_simpld (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C) p0001
  have p0003 :=
    @g_elwppcand C (.cv k) F
  have p0004 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C))) p0003
  have p0005 :=
    @g_syl (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (.classMem (.cv k) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C))) p0002 p0004
  have p0006 :=
    @g_simpld (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C)) p0005
  have p0007 :=
    @g_simpld (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C) p0006
  have p0008 :=
    @g_elhwcardswev k s e dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_biimpi (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))) p0008
  have p0010 :=
    @g_syl (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))) p0007 p0009
  have p0011 :=
    @g_simpr (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
  have p0012 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))) (syn_wbr (.cv s) (syn_cwe) (.cv e)) p0011 p0012
  have p0014 :=
    @g_simpl (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
  have p0015 :=
    @g_elwppcandstrictslice C k F
  have p0016 :=
    @g_biimpi (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C)) p0015
  have p0017 :=
    @g_simprd (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C) p0016
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wbr (.cv k) (syn_cltc) C) p0014 p0017
  have p0019 :=
    @g_simpr (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
  have p0020 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))
  have p0021 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))) (.classEq (.cv k) (syn_cnc (.cv e))) p0019 p0020
  have p0022 :=
    @g_a1i (.classEq C (syn_cnc D)) (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) hyp_wppcandstrictslicecutrepfixdrfdv_2
  have p0023 :=
    @g_breq12d (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (.cv k) (syn_cnc (.cv e)) C (syn_cnc D) (syn_cltc) p0021 p0022
  have p0024 :=
    @g_mpbid (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (syn_wbr (.cv k) (syn_cltc) C) (syn_wbr (syn_cnc (.cv e)) (syn_cltc) (syn_cnc D)) p0018 p0023
  have p0025 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (syn_wbr (.cv s) (syn_cwe) (.cv e)) (syn_wbr (syn_cnc (.cv e)) (syn_cltc) (syn_cnc D)) p0013 p0024
  have p0026 :=
    @g_wecomparisoncutreptypedtargetdfdv D R (.cv s) (.cv e) q dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_wppcandstrictslicecutrepfixdrfdv_1
  have p0027 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (syn_wbr (syn_cnc (.cv e)) (syn_cltc) (syn_cnc D))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc (.cv e)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) p0025 p0026
  have p0028 :=
    @g_simpr (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
  have p0029 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))
  have p0030 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))) (.classEq (.cv k) (syn_cnc (.cv e))) p0028 p0029
  have p0031 :=
    @g_eqeq1d (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (.cv k) (syn_cnc (.cv e)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0030
  have p0032 :=
    @g_rexbidv (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (.classEq (syn_cnc (.cv e)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) q (syn_cpw1 (syn_cpw1 D)) dv_cache_0007 p0031
  have p0033 :=
    @g_mpbird (syn_wa (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc (.cv e)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) p0027 p0032
  have p0034 :=
    @g_ex (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) p0033
  have p0035 :=
    @g_exlimdvv (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) e s dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0034
  have p0036 :=
    @g_mpd (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) p0010 p0035
  have p0037 :=
    @g_rgen (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) p0036
  exact p0037

noncomputable def g_wppcandstrictslicenonemptyminndv
    (z : Var) (C : Class) (D : Class) (R : Class) (k : Var) (n : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_q : q ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_D_k : k ∉ D.fv) (dv_D_n : n ∉ D.fv) (dv_D_q : q ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_k : k ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_R_k : k ∉ R.fv) (dv_R_n : n ∉ R.fv) (dv_R_q : q ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_k_n : k ≠ n) (dv_k_q : k ≠ q) (dv_k_z : k ≠ z) (dv_n_q : n ≠ q) (dv_n_z : n ≠ z) (dv_q_z : q ≠ z) (hyp_wppcandstrictslicenonemptyminndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wppcandstrictslicenonemptyminndv_2 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wppcandstrictslicenonemptyminndv_3 : Nominal.NPrf (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))) :
    Nominal.NPrf (.imp (syn_wne (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({k} : Finset Var) ∪ ({n} : Finset Var) ∪ F.fv ∪ ({q} : Finset Var)
  let m : Var := freshVar proofSupport 0
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_ne_z : m ≠ z := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_m : z ≠ m :=
    Ne.symm fresh_m_ne_z
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_m_not_D : m ∉ D.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_m_not_R : m ∉ R.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_m_ne_k : m ≠ k := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_k_ne_m : k ≠ m :=
    Ne.symm fresh_m_ne_k
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_m : n ≠ m :=
    Ne.symm fresh_m_ne_n
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_ne_q : m ≠ q := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_m : q ≠ m :=
    Ne.symm fresh_m_ne_q
  have dv_cache_0001 : k ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : m ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : k ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : k ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : m ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : k ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show k ≠ m from (by exact fresh_k_ne_m))
  have dv_cache_0014 : k ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show k ≠ q from (by exact dv_k_q))
  have dv_cache_0015 : m ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show m ≠ q from (by exact fresh_m_ne_q))
  have dv_cache_0016 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : k ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show k ≠ z from (by exact dv_k_z))
  have dv_cache_0019 : m ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show m ≠ z from (by exact fresh_m_ne_z))
  have dv_cache_0020 : z ∉ ((Wff.classEq (.cv n) (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_n_z), fresh_z_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : n ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : n ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : n ∉ ((syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, fresh_n_ne_m, dv_n_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : m ∉ ((syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, fresh_m_not_F, fresh_m_ne_n, fresh_m_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppcandstrictsliceleastdndvv C D R k m F q dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 hyp_wppcandstrictslicenonemptyminndv_1 hyp_wppcandstrictslicenonemptyminndv_2 hyp_wppcandstrictslicenonemptyminndv_3
  have p0001 :=
    @g_wppcandstrictsliceleastextenddv z C k m F dv_cache_0001 dv_cache_0002 dv_cache_0016 dv_cache_0007 dv_cache_0008 dv_cache_0017 dv_cache_0013 dv_cache_0018 dv_cache_0019
  have p0002 :=
    @g_id (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))))
  have p0003 :=
    @g_id (.classEq (.cv n) (.cv m))
  have p0004 :=
    @g_breq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (.cv z) (syn_clec) p0003
  have p0005 :=
    @g_ralbidv (.classEq (.cv n) (.cv m)) (syn_wbr (.cv n) (syn_clec) (.cv z)) (syn_wbr (.cv m) (syn_clec) (.cv z)) z (syn_cwppcand F C) dv_cache_0020 p0004
  have p0006 :=
    @g_rspcev (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))) n (.cv m) (syn_cwppcand F C) dv_cache_0021 dv_cache_0022 dv_cache_0023 p0005
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z)))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) p0002 p0006
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) p0001 p0007
  have p0009 :=
    @g_rexlimiva (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) dv_cache_0024 p0008
  have p0010 :=
    @g_syl (syn_wne (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) p0000 p0009
  exact p0010

#print axioms g_wppcandstrictslicenonemptyminndv

end NFChoice.DirectNominalPrf.WPPReplay
