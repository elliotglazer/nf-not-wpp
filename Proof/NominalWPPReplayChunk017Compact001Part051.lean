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
import NominalWPPReplayChunk017Compact001Part050

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

noncomputable def g_pw1xpshiftenndv
    (A : Class) (B : Class) (hyp_pw1xpshiftenndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_pw1xpshiftenndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cpw1 (syn_cxp A B)) (syn_cen) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ ((syn_cpw1 (syn_cxp A B))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_cxp A B))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_cxp (syn_cpw1 A) (syn_cpw1 B))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cxp (syn_cpw1 A) (syn_cpw1 B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0010 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_tru
  have p0001 :=
    @g_eqid (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
  have p0002 :=
    @g_simpr syn_wtru (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
  have p0003 :=
    @g_hnwpw1argcl (syn_cxp A B) p
  have p0004 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0005 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) p0003 p0004
  have p0006 :=
    @g_id (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
  have p0007 :=
    @g_n_1st2nd2 (syn_cuni (.cv p)) A B
  have p0008 :=
    @g_eleq1d (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (syn_cuni (.cv p)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cxp A B) p0007
  have p0009 :=
    @g_mpbid (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classMem (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cxp A B)) p0006 p0008
  have p0010 :=
    @g_opelxp (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) A B
  have p0011 :=
    @g_sylib (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classMem (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cxp A B)) (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)) p0009 p0010
  have p0012 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)) p0005 p0011
  have p0013 :=
    @g_simpl (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)
  have p0014 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)) (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) p0012 p0013
  have p0015 :=
    @g_snelpw1 (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A
  have p0016 :=
    @g_sylibr (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) (.classMem (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_cpw1 A)) p0014 p0015
  have p0017 :=
    @g_hnwpw1argcl (syn_cxp A B) p
  have p0018 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0019 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) p0017 p0018
  have p0020 :=
    @g_id (.classMem (syn_cuni (.cv p)) (syn_cxp A B))
  have p0021 :=
    @g_n_1st2nd2 (syn_cuni (.cv p)) A B
  have p0022 :=
    @g_eleq1d (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (syn_cuni (.cv p)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cxp A B) p0021
  have p0023 :=
    @g_mpbid (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classMem (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cxp A B)) p0020 p0022
  have p0024 :=
    @g_opelxp (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) A B
  have p0025 :=
    @g_sylib (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classMem (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cxp A B)) (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)) p0023 p0024
  have p0026 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)) p0019 p0025
  have p0027 :=
    @g_simpr (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)
  have p0028 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (syn_cuni (.cv p))) A) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B)) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B) p0026 p0027
  have p0029 :=
    @g_snelpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B
  have p0030 :=
    @g_sylibr (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) B) (.classMem (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cpw1 B)) p0028 p0029
  have p0031 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_cpw1 A)) (.classMem (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cpw1 B)) p0016 p0030
  have p0032 :=
    @g_opelxp (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cpw1 A) (syn_cpw1 B)
  have p0033 :=
    @g_sylibr (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_cpw1 A)) (.classMem (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cpw1 B))) (.classMem (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0031 p0032
  have p0034 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0002 p0033
  have p0035 :=
    @g_simpr syn_wtru (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0036 :=
    @g_id (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0037 :=
    @g_n_1st2nd2 (.cv q) (syn_cpw1 A) (syn_cpw1 B)
  have p0038 :=
    @g_eleq1d (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.cv q) (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)) p0037
  have p0039 :=
    @g_mpbid (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0036 p0038
  have p0040 :=
    @g_opelxp (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 A) (syn_cpw1 B)
  have p0041 :=
    @g_sylib (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))) p0039 p0040
  have p0042 :=
    @g_simpl (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))
  have p0043 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))) (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) p0041 p0042
  have p0044 :=
    @g_hnwpw1argclcndv (syn_cfv (syn_c1st) (.cv q)) A
  have p0045 :=
    @g_simpl (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) (.classEq (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))))
  have p0046 :=
    @g_syl (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) (.classEq (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))))) (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) p0044 p0045
  have p0047 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) p0043 p0046
  have p0048 :=
    @g_id (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0049 :=
    @g_n_1st2nd2 (.cv q) (syn_cpw1 A) (syn_cpw1 B)
  have p0050 :=
    @g_eleq1d (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.cv q) (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)) p0049
  have p0051 :=
    @g_mpbid (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0048 p0050
  have p0052 :=
    @g_opelxp (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 A) (syn_cpw1 B)
  have p0053 :=
    @g_sylib (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))) p0051 p0052
  have p0054 :=
    @g_simpr (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))
  have p0055 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B)) p0053 p0054
  have p0056 :=
    @g_hnwpw1argclcndv (syn_cfv (syn_c2nd) (.cv q)) B
  have p0057 :=
    @g_simpl (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) (.classEq (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
  have p0058 :=
    @g_syl (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B)) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) (.classEq (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))) (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) p0056 p0057
  have p0059 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B)) (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) p0055 p0058
  have p0060 :=
    @g_jca (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) p0047 p0059
  have p0061 :=
    @g_opelxp (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) A B
  have p0062 :=
    @g_sylibr (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B)) (.classMem (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) (syn_cxp A B)) p0060 p0061
  have p0063 :=
    @g_snelpw1 (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) (syn_cxp A B)
  have p0064 :=
    @g_sylibr (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) (syn_cxp A B)) (.classMem (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (syn_cpw1 (syn_cxp A B))) p0062 p0063
  have p0065 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (syn_cpw1 (syn_cxp A B))) p0035 p0064
  have p0066 :=
    @g_simpr (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
  have p0067 :=
    @g_unieqd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) p0066
  have p0068 :=
    @g_fveq2d (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cuni (.cv p)) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))) (syn_c1st) p0067
  have p0069 :=
    @g_sneqd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) p0068
  have p0070 :=
    @g_simpr (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
  have p0071 :=
    @g_unieqd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) p0070
  have p0072 :=
    @g_fveq2d (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cuni (.cv p)) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))) (syn_c2nd) p0071
  have p0073 :=
    @g_sneqd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) p0072
  have p0074 :=
    @g_opeq12d (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) p0069 p0073
  have p0075 :=
    @g_simpl (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))
  have p0076 :=
    @g_simpr syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))
  have p0077 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0078 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0076 p0077
  have p0079 :=
    @g_syl (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0075 p0078
  have p0080 :=
    @g_fvex (.cv q) (syn_c1st)
  have p0081 :=
    @g_uniex (syn_cfv (syn_c1st) (.cv q)) p0080
  have p0082 :=
    @g_fvex (.cv q) (syn_c2nd)
  have p0083 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv q)) p0082
  have p0084 :=
    @g_opex (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0081 p0083
  have p0085 :=
    @g_unisn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) p0084
  have p0086 :=
    @g_fveq2i (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) (syn_c1st) p0085
  have p0087 :=
    @g_fvex (.cv q) (syn_c1st)
  have p0088 :=
    @g_uniex (syn_cfv (syn_c1st) (.cv q)) p0087
  have p0089 :=
    @g_fvex (.cv q) (syn_c2nd)
  have p0090 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv q)) p0089
  have p0091 :=
    @g_opfv1st (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0088 p0090
  have p0092 :=
    @g_eqtri (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cfv (syn_c1st) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (syn_cuni (syn_cfv (syn_c1st) (.cv q))) p0086 p0091
  have p0093 :=
    @g_sneqi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cuni (syn_cfv (syn_c1st) (.cv q))) p0092
  have p0094 :=
    @g_fvex (.cv q) (syn_c1st)
  have p0095 :=
    @g_uniex (syn_cfv (syn_c1st) (.cv q)) p0094
  have p0096 :=
    @g_fvex (.cv q) (syn_c2nd)
  have p0097 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv q)) p0096
  have p0098 :=
    @g_opex (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0095 p0097
  have p0099 :=
    @g_unisn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) p0098
  have p0100 :=
    @g_fveq2i (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) (syn_c2nd) p0099
  have p0101 :=
    @g_fvex (.cv q) (syn_c1st)
  have p0102 :=
    @g_uniex (syn_cfv (syn_c1st) (.cv q)) p0101
  have p0103 :=
    @g_fvex (.cv q) (syn_c2nd)
  have p0104 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv q)) p0103
  have p0105 :=
    @g_opfv2nd (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0102 p0104
  have p0106 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0100 p0105
  have p0107 :=
    @g_sneqi (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) p0106
  have p0108 :=
    @g_opeq12i (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) p0093 p0107
  have p0109 :=
    @g_a1i (.classEq (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))))) (syn_cop (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0108
  have p0110 :=
    @g_n_1st2nd2 (.cv q) (syn_cpw1 A) (syn_cpw1 B)
  have p0111 :=
    @g_id (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0112 :=
    @g_n_1st2nd2 (.cv q) (syn_cpw1 A) (syn_cpw1 B)
  have p0113 :=
    @g_eleq1d (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.cv q) (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)) p0112
  have p0114 :=
    @g_mpbid (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0111 p0113
  have p0115 :=
    @g_opelxp (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 A) (syn_cpw1 B)
  have p0116 :=
    @g_sylib (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))) p0114 p0115
  have p0117 :=
    @g_simpl (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))
  have p0118 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))) (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) p0116 p0117
  have p0119 :=
    @g_hnwpw1argclcndv (syn_cfv (syn_c1st) (.cv q)) A
  have p0120 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) (.classEq (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))))) p0118 p0119
  have p0121 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) (.classEq (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))))
  have p0122 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c1st) (.cv q))) A) (.classEq (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))))) (.classEq (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q))))) p0120 p0121
  have p0123 :=
    @g_id (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0124 :=
    @g_n_1st2nd2 (.cv q) (syn_cpw1 A) (syn_cpw1 B)
  have p0125 :=
    @g_eleq1d (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.cv q) (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)) p0124
  have p0126 :=
    @g_mpbid (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) p0123 p0125
  have p0127 :=
    @g_opelxp (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 A) (syn_cpw1 B)
  have p0128 :=
    @g_sylib (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))) p0126 p0127
  have p0129 :=
    @g_simpr (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))
  have p0130 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv q)) (syn_cpw1 A)) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B))) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B)) p0128 p0129
  have p0131 :=
    @g_hnwpw1argclcndv (syn_cfv (syn_c2nd) (.cv q)) B
  have p0132 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classMem (syn_cfv (syn_c2nd) (.cv q)) (syn_cpw1 B)) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) (.classEq (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))) p0130 p0131
  have p0133 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) (.classEq (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))
  have p0134 :=
    @g_syl (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) B) (.classEq (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))) (.classEq (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) p0132 p0133
  have p0135 :=
    @g_opeq12d (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_cfv (syn_c1st) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))) (syn_cfv (syn_c2nd) (.cv q)) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) p0122 p0134
  have p0136 :=
    @g_eqtrd (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.cv q) (syn_cop (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c2nd) (.cv q))) (syn_cop (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) p0110 p0135
  have p0137 :=
    @g_eqcomd (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.cv q) (syn_cop (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) p0136
  have p0138 :=
    @g_eqtrd (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))))) (syn_cop (syn_csn (syn_cuni (syn_cfv (syn_c1st) (.cv q)))) (syn_csn (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (.cv q) p0109 p0137
  have p0139 :=
    @g_syl (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))) (.classEq (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))))) (.cv q)) p0079 p0138
  have p0140 :=
    @g_eqtrd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))))) (.cv q) p0074 p0139
  have p0141 :=
    @g_eqcomd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))))) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (.cv q) p0140
  have p0142 :=
    @g_simpr (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
  have p0143 :=
    @g_fveq2d (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_c1st) p0142
  have p0144 :=
    @g_unieqd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cfv (syn_c1st) (.cv q)) (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) p0143
  have p0145 :=
    @g_simpr (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
  have p0146 :=
    @g_fveq2d (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_c2nd) p0145
  have p0147 :=
    @g_unieqd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cfv (syn_c2nd) (.cv q)) (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) p0146
  have p0148 :=
    @g_opeq12d (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) p0144 p0147
  have p0149 :=
    @g_sneqd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))) p0148
  have p0150 :=
    @g_simpl (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
  have p0151 :=
    @g_simpr syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))
  have p0152 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))
  have p0153 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0151 p0152
  have p0154 :=
    @g_syl (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0150 p0153
  have p0155 :=
    @g_snex (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
  have p0156 :=
    @g_snex (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
  have p0157 :=
    @g_opfv1st (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0155 p0156
  have p0158 :=
    @g_unieqi (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) p0157
  have p0159 :=
    @g_fvex (syn_cuni (.cv p)) (syn_c1st)
  have p0160 :=
    @g_unisn (syn_cfv (syn_c1st) (syn_cuni (.cv p))) p0159
  have p0161 :=
    @g_eqtri (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))) (syn_cfv (syn_c1st) (syn_cuni (.cv p))) p0158 p0160
  have p0162 :=
    @g_snex (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
  have p0163 :=
    @g_snex (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
  have p0164 :=
    @g_opfv2nd (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0162 p0163
  have p0165 :=
    @g_unieqi (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0164
  have p0166 :=
    @g_fvex (syn_cuni (.cv p)) (syn_c2nd)
  have p0167 :=
    @g_unisn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) p0166
  have p0168 :=
    @g_eqtri (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) p0165 p0167
  have p0169 :=
    @g_opeq12i (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) p0161 p0168
  have p0170 :=
    @g_a1i (.classEq (syn_cop (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0169
  have p0171 :=
    @g_hnwpw1argcl (syn_cxp A B) p
  have p0172 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0173 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) p0171 p0172
  have p0174 :=
    @g_n_1st2nd2 (syn_cuni (.cv p)) A B
  have p0175 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (syn_cuni (.cv p)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) p0173 p0174
  have p0176 :=
    @g_eqtr4d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_cuni (.cv p)) p0170 p0175
  have p0177 :=
    @g_sneqd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_cop (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))))) (syn_cuni (.cv p)) p0176
  have p0178 :=
    @g_hnwpw1argcl (syn_cxp A B) p
  have p0179 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0180 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0178 p0179
  have p0181 :=
    @g_eqcomd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.cv p) (syn_csn (syn_cuni (.cv p))) p0180
  have p0182 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))))) (syn_csn (syn_cuni (.cv p))) (.cv p) p0177 p0181
  have p0183 :=
    @g_syl (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classEq (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))))) (.cv p)) p0154 p0182
  have p0184 :=
    @g_eqtrd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_cuni (syn_cfv (syn_c2nd) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))))) (.cv p) p0149 p0183
  have p0185 :=
    @g_eqcomd (syn_wa (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (.cv p) p0184
  have p0186 :=
    @g_impbida (syn_wa syn_wtru (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv q) (syn_cxp (syn_cpw1 A) (syn_cpw1 B))))) (.classEq (.cv p) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q)))))) (.classEq (.cv q) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) p0141 p0185
  have p0187 :=
    @g_f1o2d syn_wtru p q (syn_cpw1 (syn_cxp A B)) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_csn (syn_cop (syn_cuni (syn_cfv (syn_c1st) (.cv q))) (syn_cuni (syn_cfv (syn_c2nd) (.cv q))))) (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0001 p0034 p0065 p0186
  have p0188 :=
    Nominal.mp p0000 p0187
  have p0189 :=
    @g_pw1xpshiftsetndv A B p dv_cache_0010 dv_cache_0011 hyp_pw1xpshiftenndv_1 hyp_pw1xpshiftenndv_2
  have p0190 :=
    @g_f1oen (syn_cpw1 (syn_cxp A B)) (syn_cxp (syn_cpw1 A) (syn_cpw1 B)) (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) p0189
  have p0191 :=
    Nominal.mp p0188 p0190
  exact p0191

noncomputable def g_wppqkrelpw1shiftenndv
    (X : Class) (hyp_wppqkrelpw1shiftenndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cpw1 (syn_cxpk X X)) (syn_cen) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))) := by
  let proofSupport : Finset Var := X.fv
  have p0000 :=
    @g_wppqkrelrestypedenndv X X hyp_wppqkrelpw1shiftenndv_1 hyp_wppqkrelpw1shiftenndv_1
  have p0001 :=
    @g_enpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cxpk X X)
  have p0002 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cen) (syn_cxpk X X)) (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen) (syn_cpw1 (syn_cxpk X X))) p0000 p0001
  have p0003 :=
    @g_ensym (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cpw1 (syn_cxpk X X))
  have p0004 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen) (syn_cpw1 (syn_cxpk X X))) (syn_wbr (syn_cpw1 (syn_cxpk X X)) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X))))) p0002 p0003
  have p0005 :=
    @g_pw1xpshiftenndv X X hyp_wppqkrelpw1shiftenndv_1 hyp_wppqkrelpw1shiftenndv_1
  have p0006 :=
    @g_enpw1 (syn_cpw1 (syn_cxp X X)) (syn_cxp (syn_cpw1 X) (syn_cpw1 X))
  have p0007 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cxp X X)) (syn_cen) (syn_cxp (syn_cpw1 X) (syn_cpw1 X))) (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cen) (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))) p0005 p0006
  have p0008 :=
    @g_enpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))
  have p0009 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cen) (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))) (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X))))) p0007 p0008
  have p0010 :=
    @g_pw1ex X hyp_wppqkrelpw1shiftenndv_1
  have p0011 :=
    @g_pw1ex X hyp_wppqkrelpw1shiftenndv_1
  have p0012 :=
    @g_wppqkrelrestypedenndv (syn_cpw1 X) (syn_cpw1 X) p0010 p0011
  have p0013 :=
    @g_pm3_2i (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X))))) (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))) (syn_cen) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))) p0009 p0012
  have p0014 :=
    @g_entr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cpw1 X) (syn_cpw1 X)))) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_pm3_2i (syn_wbr (syn_cpw1 (syn_cxpk X X)) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X))))) (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cen) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))) p0004 p0015
  have p0017 :=
    @g_entr (syn_cpw1 (syn_cxpk X X)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))
  have p0018 :=
    Nominal.mp p0016 p0017
  exact p0018

noncomputable def g_wpplitshiftenndv
    (X : Class) (hyp_wpplitshiftenndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)) (syn_cnnc))) := by
  let proofSupport : Finset Var := X.fv
  have p0000 :=
    @g_xpkex X X hyp_wpplitshiftenndv_1 hyp_wpplitshiftenndv_1
  have p0001 :=
    @g_nncex
  have p0002 :=
    @g_pw1xpshiftenndv (syn_cxpk X X) (syn_cnnc) p0000 p0001
  have p0003 :=
    @g_wppqkrelpw1shiftenndv X hyp_wpplitshiftenndv_1
  have p0004 :=
    @g_tcnnf1o
  have p0005 :=
    @g_tcfnex
  have p0006 :=
    @g_nncex
  have p0007 :=
    @g_pw1ex (syn_cnnc) p0006
  have p0008 :=
    @g_resex (syn_ctcfn) (syn_cpw1 (syn_cnnc)) p0005 p0007
  have p0009 :=
    @g_f1oen (syn_cpw1 (syn_cnnc)) (syn_cnnc) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) p0008
  have p0010 :=
    Nominal.mp p0004 p0009
  have p0011 :=
    @g_pm3_2i (syn_wbr (syn_cpw1 (syn_cxpk X X)) (syn_cen) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X))) (syn_wbr (syn_cpw1 (syn_cnnc)) (syn_cen) (syn_cnnc)) p0003 p0010
  have p0012 :=
    @g_xpen (syn_cpw1 (syn_cxpk X X)) (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)) (syn_cpw1 (syn_cnnc)) (syn_cnnc)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_pm3_2i (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cen) (syn_cxp (syn_cpw1 (syn_cxpk X X)) (syn_cpw1 (syn_cnnc)))) (syn_wbr (syn_cxp (syn_cpw1 (syn_cxpk X X)) (syn_cpw1 (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)) (syn_cnnc))) p0002 p0013
  have p0015 :=
    @g_entr (syn_cpw1 (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cxp (syn_cpw1 (syn_cxpk X X)) (syn_cpw1 (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 X) (syn_cpw1 X)) (syn_cnnc))
  have p0016 :=
    Nominal.mp p0014 p0015
  exact p0016

#print axioms g_wpplitshiftenndv

end NFChoice.DirectNominalPrf.WPPReplay
