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
import NominalWPPReplayChunk017Compact001Part086

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

noncomputable def g_ncwehwcardsndv
    (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) D) (.classMem (syn_cnc D) (syn_chwcards (syn_cvv)))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let s : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_s_ne_d : s ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_s : d ≠ s :=
    Ne.symm fresh_s_ne_d
  have dv_cache_0001 : d ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : s ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : s ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_R, fresh_s_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : d ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0008 : d ∉ ((syn_cnc D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : s ∉ ((syn_cnc D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex R D (syn_cwe)
  have p0001 :=
    @g_ancomd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0000
  have p0002 :=
    @g_simpl (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0003 :=
    @g_eqcomd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv d) D p0002
  have p0004 :=
    @g_nceqd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) D (.cv d) p0003
  have p0005 :=
    @g_biantrud (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.classEq (syn_cnc D) (syn_cnc (.cv d))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) p0004
  have p0006 :=
    @g_bicomd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_cnc D) (syn_cnc (.cv d)))) p0005
  have p0007 :=
    @g_simpr (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0008 :=
    @g_simpl (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0009 :=
    @g_breq12d (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv s) R (.cv d) D (syn_cwe) p0007 p0008
  have p0010 :=
    @g_bitrd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_cnc D) (syn_cnc (.cv d)))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wbr R (syn_cwe) D) p0006 p0009
  have p0011 :=
    @g_spc2egv (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_cnc D) (syn_cnc (.cv d)))) (syn_wbr R (syn_cwe) D) d s D R (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0010
  have p0012 :=
    @g_syl (syn_wbr R (syn_cwe) D) (syn_wa (.classMem D (syn_cvv)) (.classMem R (syn_cvv))) (.imp (syn_wbr R (syn_cwe) D) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_cnc D) (syn_cnc (.cv d))))))) p0001 p0011
  have p0013 :=
    @g_pm2_43i (syn_wbr R (syn_cwe) D) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_cnc D) (syn_cnc (.cv d)))))) p0012
  have p0014 :=
    @g_ncex D
  have p0015 :=
    @g_elhwcardsweclndv (syn_cnc D) s d dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_sylibr (syn_wbr R (syn_cwe) D) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_cnc D) (syn_cnc (.cv d)))))) (.classMem (syn_cnc D) (syn_chwcards (syn_cvv))) p0013 p0016
  exact p0017

noncomputable def g_hnsiquomaprepvalcl3ndv
    (A : Class) (C : Class) (Q : Class) (hyp_hnsiquomaprepvalcl3ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) Q) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))) := by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ Q.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (Q).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.imp (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) Q) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_Q, fresh_q_not_A, fresh_q_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))
  have p0001 :=
    @g_elex Q (syn_cpw1 (syn_chnord A))
  have p0002 :=
    @g_syl (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))) (.classMem Q (syn_cpw1 (syn_chnord A))) (.classMem Q (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_id (.classEq (.cv q) Q)
  have p0004 :=
    @g_eleq1d (.classEq (.cv q) Q) (.cv q) Q (syn_cpw1 (syn_chnord A)) p0003
  have p0005 :=
    @g_biid (.classMem C (syn_chwcn A))
  have p0006 :=
    @g_a1i (syn_wb (.classMem C (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classEq (.cv q) Q) p0005
  have p0007 :=
    @g_id (.classEq (.cv q) Q)
  have p0008 :=
    @g_unieqd (.classEq (.cv q) Q) (.cv q) Q p0007
  have p0009 :=
    @g_eqeq1d (.classEq (.cv q) Q) (syn_cuni (.cv q)) (syn_cuni Q) (syn_cec C (syn_chwniso A)) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv q) Q) (.classMem C (syn_chwcn A)) (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))) p0006 p0009
  have p0011 :=
    @g_anbi12d (.classEq (.cv q) Q) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A)))) p0004 p0010
  have p0012 :=
    @g_id (.classEq (.cv q) Q)
  have p0013 :=
    @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsiquomap A) p0012
  have p0014 :=
    @g_eqeq1d (.classEq (.cv q) Q) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) Q) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))) p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv q) Q) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))) (.classEq (syn_cfv (syn_chnsiquomap A) Q) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))) p0011 p0014
  have p0016 :=
    @g_hnsiquomaprepvalcl2ndv A C q dv_cache_0001 hyp_hnsiquomaprepvalcl3ndv_1
  have p0017 :=
    @g_vtoclg (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))) (.imp (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) Q) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))) q Q (syn_cvv) dv_cache_0002 dv_cache_0003 p0015 p0016
  have p0018 :=
    @g_syl (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))) (.classMem Q (syn_cvv)) (.imp (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) Q) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))) p0002 p0017
  have p0019 :=
    @g_pm2_43i (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) Q) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))) p0018
  exact p0019

#print axioms g_hnsiquomaprepvalcl3ndv

end NFChoice.DirectNominalPrf.WPPReplay
