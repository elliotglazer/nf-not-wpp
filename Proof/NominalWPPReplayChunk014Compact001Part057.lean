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
import NominalWPPReplayChunk014Compact001Part056

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

noncomputable def g_finleaststep
    (y : Var) (z : Var) (u : Var) (t : Var) (A : Class) (X : Class) (dv_A_t : t ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_X_t : t ∉ X.fv) (dv_X_u : u ∉ X.fv) (dv_X_y : y ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_t_u : t ≠ u) (dv_t_y : t ≠ y) (dv_t_z : t ≠ z) (dv_u_y : u ≠ y) (dv_u_z : u ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.imp (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ({u} : Finset Var) ∪ ({t} : Finset Var) ∪ A.fv ∪ X.fv
  have dv_cache_0001 : u ∉ ((Class.cv t)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_t_u), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (X).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_t_u), dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_u_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ ((syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_u_y, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_X_y, (Ne.symm dv_u_y), (Ne.symm dv_t_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.classEq (.cv z) (syn_cplc A (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_y_z, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_cplc A (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_wral y X (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_z, dv_A_z, (Ne.symm dv_y_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_t, dv_t_z, dv_t_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : t ∉ ((syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_t, dv_X_t, dv_t_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))
  have p0001 :=
    @g_simpr (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))
  have p0004 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))
  have p0005 :=
    @g_simpl (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
  have p0006 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) p0004 p0005
  have p0007 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) p0003 p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0009 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.classMem (.cv t) X) p0008 p0009
  have p0011 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0012 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0013 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0014 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0015 :=
    @g_simpl (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.classMem A (syn_cnnc)) p0014 p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem A (syn_cnnc)) p0013 p0016
  have p0018 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0019 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0020 :=
    @g_simpr (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wss X (syn_cnnc)) p0019 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wss X (syn_cnnc)) p0018 p0021
  have p0023 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0024 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) X (syn_cnnc) (.cv t) p0022 p0023
  have p0025 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.classMem A (syn_cnnc)) (.classMem (.cv t) (syn_cnnc)) p0017 p0024
  have p0026 :=
    @g_kqfinsucsplit A (.cv t)
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv t) (syn_cnnc))) (syn_wb (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv t) (syn_cplc A (syn_c1c))))) p0025 p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wb (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv t) (syn_cplc A (syn_c1c))))) p0012 p0027
  have p0029 :=
    @g_biimpd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv t) (syn_cplc A (syn_c1c)))) p0028
  have p0030 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv t) (syn_cplc A (syn_c1c)))) p0011 p0029
  have p0031 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0032 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0033 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) p0032 p0033
  have p0035 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
  have p0036 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.classMem (.cv t) X) p0035 p0036
  have p0038 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
  have p0039 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)) (.classMem (.cv t) X) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) p0037 p0038
  have p0040 :=
    @g_breq1 (.cv u) (.cv t) A (syn_ckqrel (syn_clefin))
  have p0041 :=
    @g_rspcev (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) u (.cv t) X dv_cache_0001 dv_cache_0002 dv_cache_0003 p0040
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)) (syn_wa (.classMem (.cv t) X) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0039 p0041
  have p0043 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0042
  have p0044 :=
    @g_con3d (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0043
  have p0045 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (.neg (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)) p0034 p0044
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.neg (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)) p0031 p0045
  have p0047 :=
    @g_pm2_21d (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv t) (syn_cplc A (syn_c1c))) p0046
  have p0048 :=
    @g_id (.classEq (.cv t) (syn_cplc A (syn_c1c)))
  have p0049 :=
    @g_a1i (.imp (.classEq (.cv t) (syn_cplc A (syn_c1c))) (.classEq (.cv t) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) p0048
  have p0050 :=
    @g_jaod (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv t) (syn_cplc A (syn_c1c))) (.classEq (.cv t) (syn_cplc A (syn_c1c))) p0047 p0049
  have p0051 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv t) (syn_cplc A (syn_c1c)))) (.classEq (.cv t) (syn_cplc A (syn_c1c))) p0030 p0050
  have p0052 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.cv t) (syn_cplc A (syn_c1c)) X p0051
  have p0053 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv t) X) (.classMem (syn_cplc A (syn_c1c)) X) p0010 p0052
  have p0054 :=
    @g_finleor
  have p0055 :=
    @g_sopc (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0056 :=
    @g_biimpi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc)) (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc))) p0055
  have p0057 :=
    Nominal.mp p0054 p0056
  have p0058 :=
    @g_simpr (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc))
  have p0059 :=
    Nominal.mp p0057 p0058
  have p0060 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) p0059
  have p0061 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0062 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) p0061 p0062
  have p0064 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0065 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0066 :=
    @g_simpl (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0067 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.classMem A (syn_cnnc)) p0065 p0066
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem A (syn_cnnc)) p0064 p0067
  have p0069 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.classMem A (syn_cnnc)) p0063 p0068
  have p0070 :=
    @g_peano2 A
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0069 p0070
  have p0072 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0073 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) p0072 p0073
  have p0075 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0076 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0077 :=
    @g_simpr (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0078 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wss X (syn_cnnc)) p0076 p0077
  have p0079 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wss X (syn_cnnc)) p0075 p0078
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wss X (syn_cnnc)) p0074 p0079
  have p0081 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0082 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) X (syn_cnnc) (.cv y) p0080 p0081
  have p0083 :=
    @g_connexd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_cnnc) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)) (.cv y) p0060 p0071 p0082
  have p0084 :=
    @g_id (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0085 :=
    @g_a1i (.imp (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) p0084
  have p0086 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0087 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0088 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0089 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) p0087 p0088
  have p0090 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0091 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0092 :=
    @g_simpl (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0093 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.classMem A (syn_cnnc)) p0091 p0092
  have p0094 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem A (syn_cnnc)) p0090 p0093
  have p0095 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.classMem A (syn_cnnc)) p0089 p0094
  have p0096 :=
    @g_peano2 A
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0095 p0096
  have p0098 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0086 p0097
  have p0099 :=
    @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0100 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0098 p0099
  have p0101 :=
    @g_lefinrflx (syn_cplc A (syn_c1c)) (syn_cvv)
  have p0102 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin)) p0100 p0101
  have p0103 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0104 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0105 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0106 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) p0104 p0105
  have p0107 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0108 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0109 :=
    @g_simpl (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0110 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.classMem A (syn_cnnc)) p0108 p0109
  have p0111 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem A (syn_cnnc)) p0107 p0110
  have p0112 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.classMem A (syn_cnnc)) p0106 p0111
  have p0113 :=
    @g_peano2 A
  have p0114 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0112 p0113
  have p0115 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0103 p0114
  have p0116 :=
    @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0117 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0115 p0116
  have p0118 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0119 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0120 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0121 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) p0119 p0120
  have p0122 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0123 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0124 :=
    @g_simpl (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0125 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.classMem A (syn_cnnc)) p0123 p0124
  have p0126 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem A (syn_cnnc)) p0122 p0125
  have p0127 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.classMem A (syn_cnnc)) p0121 p0126
  have p0128 :=
    @g_peano2 A
  have p0129 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0127 p0128
  have p0130 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0118 p0129
  have p0131 :=
    @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0132 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0130 p0131
  have p0133 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0117 p0132
  have p0134 :=
    @g_kqlefinbr (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c)) (syn_cvv) (syn_cvv)
  have p0135 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))) (syn_wb (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin))) p0133 p0134
  have p0136 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin)) p0102 p0135
  have p0137 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0138 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0139 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0140 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0141 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) p0139 p0140
  have p0142 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0143 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0144 :=
    @g_simpl (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0145 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.classMem A (syn_cnnc)) p0143 p0144
  have p0146 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem A (syn_cnnc)) p0142 p0145
  have p0147 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.classMem A (syn_cnnc)) p0141 p0146
  have p0148 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0149 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0150 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) p0148 p0149
  have p0151 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0152 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0153 :=
    @g_simpr (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0154 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wss X (syn_cnnc)) p0152 p0153
  have p0155 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wss X (syn_cnnc)) p0151 p0154
  have p0156 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wss X (syn_cnnc)) p0150 p0155
  have p0157 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0158 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) X (syn_cnnc) (.cv y) p0156 p0157
  have p0159 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.classMem A (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) p0147 p0158
  have p0160 :=
    @g_kqfinsucsplit A (.cv y)
  have p0161 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv y) (syn_cplc A (syn_c1c))))) p0159 p0160
  have p0162 :=
    @g_biimpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv y) (syn_cplc A (syn_c1c)))) p0161
  have p0163 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv y) (syn_cplc A (syn_c1c))))) p0138 p0162
  have p0164 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv y) (syn_cplc A (syn_c1c)))) p0137 p0163
  have p0165 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0166 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0167 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0168 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) p0166 p0167
  have p0169 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)
  have p0170 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0171 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) p0169 p0170
  have p0172 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) p0168 p0171
  have p0173 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
  have p0174 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)
  have p0175 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.classMem (.cv y) X) p0173 p0174
  have p0176 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
  have p0177 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)) (.classMem (.cv y) X) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) p0175 p0176
  have p0178 :=
    @g_breq1 (.cv u) (.cv y) A (syn_ckqrel (syn_clefin))
  have p0179 :=
    @g_rspcev (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) u (.cv y) X dv_cache_0004 dv_cache_0002 dv_cache_0005 p0178
  have p0180 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)) (syn_wa (.classMem (.cv y) X) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0177 p0179
  have p0181 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0180
  have p0182 :=
    @g_con3d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0181
  have p0183 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (.neg (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)) p0172 p0182
  have p0184 :=
    @g_pm2_21d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv y) (syn_cplc A (syn_c1c))) p0183
  have p0185 :=
    @g_id (.classEq (.cv y) (syn_cplc A (syn_c1c)))
  have p0186 :=
    @g_a1i (.imp (.classEq (.cv y) (syn_cplc A (syn_c1c))) (.classEq (.cv y) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) p0185
  have p0187 :=
    @g_jaod (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv y) (syn_cplc A (syn_c1c))) (.classEq (.cv y) (syn_cplc A (syn_c1c))) p0184 p0186
  have p0188 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (.imp (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv y) (syn_cplc A (syn_c1c)))) (.classEq (.cv y) (syn_cplc A (syn_c1c)))) p0165 p0187
  have p0189 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) (.classEq (.cv y) (syn_cplc A (syn_c1c)))) (.classEq (.cv y) (syn_cplc A (syn_c1c))) p0164 p0188
  have p0190 :=
    @g_breq2d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.cv y) (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) p0189
  have p0191 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) p0136 p0190
  have p0192 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0191
  have p0193 :=
    @g_jaod (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) p0085 p0192
  have p0194 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (.cv y) X)) (syn_wo (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0083 p0193
  have p0195 :=
    @g_ralrimiva (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) y X dv_cache_0006 p0194
  have p0196 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (.classMem (syn_cplc A (syn_c1c)) X) (syn_wral y X (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) p0053 p0195
  have p0197 :=
    @g_breq1 (.cv z) (syn_cplc A (syn_c1c)) (.cv y) (syn_ckqrel (syn_clefin))
  have p0198 :=
    @g_ralbidv (.classEq (.cv z) (syn_cplc A (syn_c1c))) (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) y X dv_cache_0007 p0197
  have p0199 :=
    @g_rspcev (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wral y X (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) z (syn_cplc A (syn_c1c)) X dv_cache_0008 dv_cache_0009 dv_cache_0010 p0198
  have p0200 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wa (.classMem (syn_cplc A (syn_c1c)) X) (syn_wral y X (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0196 p0199
  have p0201 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0200
  have p0202 :=
    @g_rexlimdva (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) t X dv_cache_0011 dv_cache_0012 p0201
  have p0203 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))) (.imp (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) p0007 p0202
  have p0204 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0002 p0203
  have p0205 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0204
  exact p0205

#print axioms g_finleaststep

end NFChoice.DirectNominalPrf.WPPReplay
