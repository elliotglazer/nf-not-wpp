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
import NominalWPPReplayChunk017Compact001Part009

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

noncomputable def g_hnsiquomapfvineqndv
    (A : Class) (s : Var) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_s : s ∉ A.fv) (dv_q_s : q ≠ s) (hyp_hnsiquomapfvineqndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))) := by
  let proofSupport : Finset Var := A.fv ∪ ({s} : Finset Var) ∪ ({q} : Finset Var)
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_ne_s : u ≠ s := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_u : s ≠ u :=
    Ne.symm fresh_u_ne_s
  have fresh_u_ne_q : u ≠ q := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_u : q ≠ u :=
    Ne.symm fresh_u_ne_q
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_ne_s : v ≠ s := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_v : s ≠ v :=
    Ne.symm fresh_v_ne_s
  have fresh_v_ne_q : v ≠ q := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_v : q ≠ v :=
    Ne.symm fresh_v_ne_q
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_cuni (.cv q))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((syn_cuni (.cv s))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0007 : s ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : s ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show s ≠ v from (by exact fresh_s_ne_v))
  have dv_cache_0009 : Disjoint ((Class.cv u)).fv ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint ((Class.cv u)).fv ((syn_chwniso A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso]; exact (show Disjoint (({u} : Finset Var)) ((A).fv) from (Finset.disjoint_singleton_left.mpr (show u ∉ (A).fv from (by exact fresh_u_not_A))))))
  have dv_cache_0010 : v ∉ ((Wff.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_q, fresh_v_not_A, fresh_v_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_q, fresh_v_not_A, fresh_v_ne_s, fresh_v_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((Wff.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, fresh_u_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : u ∉ ((syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, fresh_u_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0001 :=
    @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0000 p0001
  have p0003 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) p0002 p0003
  have p0005 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0006 :=
    @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0005 p0006
  have p0008 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) p0007 p0008
  have p0010 :=
    @g_elex (syn_cuni (.cv q)) (syn_chnord A)
  have p0011 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_elhnordclndv u A (syn_cuni (.cv q)) dv_cache_0001 dv_cache_0002
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (syn_cuni (.cv q)) (syn_cvv)) (syn_wb (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0011 p0012
  have p0014 :=
    @g_mpbid (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0004 p0013
  have p0015 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0016 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0017 :=
    @g_pw1argclcl (syn_chnord A) (.cv s)
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (.classEq (.cv s) (syn_csn (syn_cuni (.cv s))))) p0016 p0017
  have p0019 :=
    @g_simpl (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (.classEq (.cv s) (syn_csn (syn_cuni (.cv s))))
  have p0020 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (.classEq (.cv s) (syn_csn (syn_cuni (.cv s))))) (.classMem (syn_cuni (.cv s)) (syn_chnord A)) p0018 p0019
  have p0021 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0022 :=
    @g_pw1argclcl (syn_chnord A) (.cv s)
  have p0023 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (.classEq (.cv s) (syn_csn (syn_cuni (.cv s))))) p0021 p0022
  have p0024 :=
    @g_simpl (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (.classEq (.cv s) (syn_csn (syn_cuni (.cv s))))
  have p0025 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (.classEq (.cv s) (syn_csn (syn_cuni (.cv s))))) (.classMem (syn_cuni (.cv s)) (syn_chnord A)) p0023 p0024
  have p0026 :=
    @g_elex (syn_cuni (.cv s)) (syn_chnord A)
  have p0027 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (.classMem (syn_cuni (.cv s)) (syn_cvv)) p0025 p0026
  have p0028 :=
    @g_elhnordclndv v A (syn_cuni (.cv s)) dv_cache_0003 dv_cache_0004
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (syn_cuni (.cv s)) (syn_cvv)) (syn_wb (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (syn_wrex v (syn_chwcn A) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) p0027 p0028
  have p0030 :=
    @g_mpbid (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (syn_wrex v (syn_chwcn A) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0020 p0029
  have p0031 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wrex v (syn_chwcn A) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0015 p0030
  have p0032 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0033 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0032 p0033
  have p0035 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) p0034 p0035
  have p0037 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0036 p0037
  have p0039 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0040 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0039 p0040
  have p0042 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0041 p0042
  have p0044 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (.cv u) (syn_chwcn A)) p0043 p0044
  have p0046 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0047 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0046 p0047
  have p0049 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0050 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0048 p0049
  have p0051 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0052 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0050 p0051
  have p0053 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0045 p0052
  have p0054 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0038 p0053
  have p0055 :=
    @g_hnordpw1repndv u A q dv_cache_0005 dv_cache_0001 dv_cache_0006
  have p0056 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classEq (.cv q) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))) p0054 p0055
  have p0057 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0058 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0059 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0057 p0058
  have p0060 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) p0059 p0060
  have p0062 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0061 p0062
  have p0064 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0065 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0066 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0064 p0065
  have p0067 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0066 p0067
  have p0069 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0070 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (.cv u) (syn_chwcn A)) p0068 p0069
  have p0071 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0072 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0073 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0071 p0072
  have p0074 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0075 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0073 p0074
  have p0076 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0077 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0075 p0076
  have p0078 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0070 p0077
  have p0079 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0063 p0078
  have p0080 :=
    @g_hnsiquomaprepvalndv u A q dv_cache_0005 dv_cache_0001 dv_cache_0006 hyp_hnsiquomapfvineqndv_1
  have p0081 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))) p0079 p0080
  have p0082 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) p0081
  have p0083 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0084 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)) p0082 p0083
  have p0085 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0086 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0087 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0085 p0086
  have p0088 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0089 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) p0087 p0088
  have p0090 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) p0089 p0090
  have p0092 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0093 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0094 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0092 p0093
  have p0095 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0096 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) (.classMem (.cv v) (syn_chwcn A)) p0094 p0095
  have p0097 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0098 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0099 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0097 p0098
  have p0100 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0101 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))) p0099 p0100
  have p0102 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))) p0096 p0101
  have p0103 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0091 p0102
  have p0104 :=
    @g_hnsiquomaprepvalndv v A s dv_cache_0007 dv_cache_0003 dv_cache_0008 hyp_hnsiquomapfvineqndv_1
  have p0105 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv s)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwniso (syn_cpw1 A)))) p0103 p0104
  have p0106 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) (syn_cfv (syn_chnsiquomap A) (.cv s)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwniso (syn_cpw1 A))) p0084 p0105
  have p0107 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0108 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0109 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0107 p0108
  have p0110 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0111 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0109 p0110
  have p0112 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0113 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (.cv u) (syn_chwcn A)) p0111 p0112
  have p0114 :=
    @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0115 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0113 p0114
  have p0116 :=
    @g_hnsicodemapfndv A
  have p0117 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv u)) (syn_chnsicodemap A) p0116
  have p0118 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A))) p0115 p0117
  have p0119 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0120 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0121 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0119 p0120
  have p0122 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0123 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) (.classMem (.cv v) (syn_chwcn A)) p0121 p0122
  have p0124 :=
    @g_snelpw1 (.cv v) (syn_chwcn A)
  have p0125 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0123 p0124
  have p0126 :=
    @g_hnsicodemapfndv A
  have p0127 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv v)) (syn_chnsicodemap A) p0126
  have p0128 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A))) p0125 p0127
  have p0129 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A))) p0118 p0128
  have p0130 :=
    @g_pw1exg A (syn_cvv)
  have p0131 :=
    Nominal.mp hyp_hnsiquomapfvineqndv_1 p0130
  have p0132 :=
    @g_hwnisoclasseqbcl (syn_cpw1 A) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) p0131
  have p0133 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A)))) (syn_wb (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwniso (syn_cpw1 A)))) (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) p0129 p0132
  have p0134 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwniso (syn_cpw1 A)))) (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) p0106 p0133
  have p0135 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0136 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0137 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0135 p0136
  have p0138 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0139 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) (.classMem (.cv v) (syn_chwcn A)) p0137 p0138
  have p0140 :=
    @g_snelpw1 (.cv v) (syn_chwcn A)
  have p0141 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0139 p0140
  have p0142 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0143 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0144 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0142 p0143
  have p0145 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0146 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0144 p0145
  have p0147 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0148 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (.cv u) (syn_chwcn A)) p0146 p0147
  have p0149 :=
    @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0150 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0148 p0149
  have p0151 :=
    @g_hnsicodemapkernelcl2ndv A (syn_csn (.cv v)) (syn_csn (.cv u))
  have p0152 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.imp (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v))) (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) p0150 p0151
  have p0153 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v))) (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) p0141 p0152
  have p0154 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v))) (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) p0134 p0153
  have p0155 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0156 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0157 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0155 p0156
  have p0158 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0159 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0157 p0158
  have p0160 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0161 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (.cv u) (syn_chwcn A)) p0159 p0160
  have p0162 :=
    @g_elex (.cv u) (syn_chwcn A)
  have p0163 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv)) p0161 p0162
  have p0164 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0165 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0166 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0164 p0165
  have p0167 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0168 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) (.classMem (.cv v) (syn_chwcn A)) p0166 p0167
  have p0169 :=
    @g_elex (.cv v) (syn_chwcn A)
  have p0170 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_cvv)) p0168 p0169
  have p0171 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv u) (syn_cvv)) (.classMem (.cv v) (syn_cvv)) p0163 p0170
  have p0172 :=
    @g_brsnsiandv (.cv u) (.cv v) (syn_chwniso A) dv_cache_0009
  have p0173 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (.cv v) (syn_cvv))) (syn_wb (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) p0171 p0172
  have p0174 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0154 p0173
  have p0175 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0176 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0177 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0175 p0176
  have p0178 :=
    @g_simpr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0179 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0177 p0178
  have p0180 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0181 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (.cv u) (syn_chwcn A)) p0179 p0180
  have p0182 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0183 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0184 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0182 p0183
  have p0185 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0186 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) (.classMem (.cv v) (syn_chwcn A)) p0184 p0185
  have p0187 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0181 p0186
  have p0188 :=
    @g_hwnisoclasseqbcl A (.cv u) (.cv v) hyp_hnsiquomapfvineqndv_1
  have p0189 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) p0187 p0188
  have p0190 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0174 p0189
  have p0191 :=
    @g_sneq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))
  have p0192 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (.classEq (syn_csn (syn_cec (.cv u) (syn_chwniso A))) (syn_csn (syn_cec (.cv v) (syn_chwniso A)))) p0190 p0191
  have p0193 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.cv q) (syn_csn (syn_cec (.cv u) (syn_chwniso A))) (syn_csn (syn_cec (.cv v) (syn_chwniso A))) p0056 p0192
  have p0194 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0195 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0196 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0194 p0195
  have p0197 :=
    @g_simpl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0198 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) p0196 p0197
  have p0199 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0200 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) p0198 p0199
  have p0201 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0202 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0203 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0201 p0202
  have p0204 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0205 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) (.classMem (.cv v) (syn_chwcn A)) p0203 p0204
  have p0206 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0207 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0208 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0206 p0207
  have p0209 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0210 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))) p0208 p0209
  have p0211 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))) p0205 p0210
  have p0212 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))) p0200 p0211
  have p0213 :=
    @g_hnordpw1repndv v A s dv_cache_0007 dv_cache_0003 dv_cache_0008
  have p0214 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (.cv s) (syn_csn (syn_cec (.cv v) (syn_chwniso A)))) p0212 p0213
  have p0215 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.cv s) (syn_csn (syn_cec (.cv v) (syn_chwniso A))) p0214
  have p0216 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))) (.cv q) (syn_csn (syn_cec (.cv v) (syn_chwniso A))) (.cv s) p0193 p0215
  have p0217 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)) p0216
  have p0218 :=
    @g_rexlimddv (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))) (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))) v (syn_chwcn A) dv_cache_0010 dv_cache_0011 p0031 p0217
  have p0219 :=
    @g_rexlimddv (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))) u (syn_chwcn A) dv_cache_0012 dv_cache_0013 p0014 p0218
  exact p0219

#print axioms g_hnsiquomapfvineqndv

end NFChoice.DirectNominalPrf.WPPReplay
