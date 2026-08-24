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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk009StructuralPart056


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

noncomputable def g_tfinltfinlem1
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.imp (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_tfinnnul M
  have p0001 :=
    @g_ex (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wne (syn_ctfin M) (syn_c0)) p0000
  have p0002 :=
    @g_adantrd (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))) p0001
  have p0003 :=
    @g_adantr (.classMem M (syn_cnnc)) (.imp (syn_wa (syn_wne M (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_wne (syn_ctfin M) (syn_c0))) (.classMem N (syn_cnnc)) p0002
  have p0004 :=
    @g_addcnul1 (syn_c1c)
  have p0005 :=
    @g_addccom (syn_c1c) (syn_c0)
  have p0006 :=
    @g_eqtr3i (syn_cplc (syn_c1c) (syn_c0)) (syn_c0) (syn_cplc (syn_c0) (syn_c1c)) p0004 p0005
  have p0007 :=
    @g_addceq2 (.cv y) (syn_c0) (syn_ctfin M)
  have p0008 :=
    @g_addcnul1 (syn_ctfin M)
  have p0009 :=
    @g_syl6eq (.classEq (.cv y) (syn_c0)) (syn_cplc (syn_ctfin M) (.cv y)) (syn_cplc (syn_ctfin M) (syn_c0)) (syn_c0) p0007 p0008
  have p0010 :=
    @g_addceq1d (.classEq (.cv y) (syn_c0)) (syn_cplc (syn_ctfin M) (.cv y)) (syn_c0) (syn_c1c) p0009
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_c0)) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)) (syn_cplc (syn_c0) (syn_c1c)) (syn_c0) p0010
  have p0012 :=
    @g_rspcev (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))) (.classEq (syn_c0) (syn_cplc (syn_c0) (syn_c1c))) y (syn_c0) (syn_cnnc) (by exact (show y ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((Wff.classEq (syn_c0) (syn_cplc (syn_c0) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((syn_c0)).fv) ∪ (((syn_cplc (syn_c0) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_cplc (syn_c0) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((syn_c0)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0011
  have p0013 :=
    @g_mpan2 (.classMem (syn_c0) (syn_cnnc)) (.classEq (syn_c0) (syn_cplc (syn_c0) (syn_c1c))) (syn_wrex y (syn_cnnc) (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) p0006 p0012
  have p0014 :=
    @g_eleq1 N (syn_c0) (syn_cnnc)
  have p0015 :=
    @g_tfineq N (syn_c0)
  have p0016 :=
    @g_tfinnul
  have p0017 :=
    @g_syl6eq (.classEq N (syn_c0)) (syn_ctfin N) (syn_ctfin (syn_c0)) (syn_c0) p0015 p0016
  have p0018 :=
    @g_eqeq1d (.classEq N (syn_c0)) (syn_ctfin N) (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)) p0017
  have p0019 :=
    @g_rexbidv (.classEq N (syn_c0)) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))) (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))) y (syn_cnnc) (by exact (show y ∉ ((Wff.classEq N (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((N).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (N).fv from (by exact fresh_y_not_N)) (show y ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0018
  have p0020 :=
    @g_imbi12d (.classEq N (syn_c0)) (.classMem N (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc)) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) p0014 p0019
  have p0021 :=
    @g_mpbiri (.classEq N (syn_c0)) (.imp (.classMem N (syn_cnnc)) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))) (.imp (.classMem (syn_c0) (syn_cnnc)) (syn_wrex y (syn_cnnc) (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))) p0013 p0020
  have p0022 :=
    @g_adantld (.classEq N (syn_c0)) (.classMem N (syn_cnnc)) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) (.classMem M (syn_cnnc)) p0021
  have p0023 :=
    @g_adantrd (.classEq N (syn_c0)) (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) p0022
  have p0024 :=
    @g_a1dd (.classEq N (syn_c0)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) p0023
  have p0025 :=
    @g_simp2r (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
  have p0026 :=
    @g_simp3r (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))
  have p0027 :=
    @g_simp3l (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))
  have p0028 :=
    @g_eqnetrrd (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)) (syn_c0) p0026 p0027
  have p0029 :=
    @g_addcnnul (syn_cplc M (.cv x)) (syn_c1c)
  have p0030 :=
    @g_syl (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_wne (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)) (syn_c0)) (syn_wa (syn_wne (syn_cplc M (.cv x)) (syn_c0)) (syn_wne (syn_c1c) (syn_c0))) p0028 p0029
  have p0031 :=
    @g_simpld (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_wne (syn_cplc M (.cv x)) (syn_c0)) (syn_wne (syn_c1c) (syn_c0)) p0030
  have p0032 :=
    @g_addcnnul M (.cv x)
  have p0033 :=
    @g_syl (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_wne (syn_cplc M (.cv x)) (syn_c0)) (syn_wa (syn_wne M (syn_c0)) (syn_wne (.cv x) (syn_c0))) p0031 p0032
  have p0034 :=
    @g_simprd (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_wne M (syn_c0)) (syn_wne (.cv x) (syn_c0)) p0033
  have p0035 :=
    @g_tfinprop (.cv x) y (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))
  have p0036 :=
    @g_simpld (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))) (.classMem (syn_ctfin (.cv x)) (syn_cnnc)) (syn_wrex y (.cv x) (.classMem (syn_cpw1 (.cv y)) (syn_ctfin (.cv x)))) p0035
  have p0037 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (.classMem (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)) (.classMem (syn_ctfin (.cv x)) (syn_cnnc)) p0025 p0034 p0036
  have p0038 :=
    @g_tfineq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))
  have p0039 :=
    @g_adantl (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (.classEq (syn_ctfin N) (syn_ctfin (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))) (syn_wne N (syn_c0)) p0038
  have p0040 :=
    @g_n_3ad2ant3 (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))) (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_ctfin N) (syn_ctfin (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) p0039
  have p0041 :=
    @g_simp1l (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
  have p0042 :=
    @g_nncaddccl M (.cv x)
  have p0043 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (.classMem M (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (.classMem (syn_cplc M (.cv x)) (syn_cnnc)) p0041 p0025 p0042
  have p0044 :=
    @g_tfinsuc (syn_cplc M (.cv x))
  have p0045 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (.classMem (syn_cplc M (.cv x)) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_cplc (syn_ctfin (syn_cplc M (.cv x))) (syn_c1c))) p0043 p0028 p0044
  have p0046 :=
    @g_eqtrd (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_ctfin N) (syn_ctfin (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_cplc (syn_ctfin (syn_cplc M (.cv x))) (syn_c1c)) p0040 p0045
  have p0047 :=
    @g_tfindi M (.cv x)
  have p0048 :=
    @g_syl3anc (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (.classMem M (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (syn_wne (syn_cplc M (.cv x)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc M (.cv x))) (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x)))) p0041 p0025 p0031 p0047
  have p0049 :=
    @g_addceq1d (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_ctfin (syn_cplc M (.cv x))) (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c) p0048
  have p0050 :=
    @g_eqtrd (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_ctfin N) (syn_cplc (syn_ctfin (syn_cplc M (.cv x))) (syn_c1c)) (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c)) p0046 p0049
  have p0051 :=
    @g_addceq2 (.cv y) (syn_ctfin (.cv x)) (syn_ctfin M)
  have p0052 :=
    @g_addceq1d (.classEq (.cv y) (syn_ctfin (.cv x))) (syn_cplc (syn_ctfin M) (.cv y)) (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c) p0051
  have p0053 :=
    @g_eqeq2d (.classEq (.cv y) (syn_ctfin (.cv x))) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c)) (syn_ctfin N) p0052
  have p0054 :=
    @g_rspcev (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c))) y (syn_ctfin (.cv x)) (syn_cnnc) (by exact (show y ∉ ((syn_ctfin (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))) (by exact (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((Wff.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((syn_ctfin N)).fv) ∪ (((syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show y ∉ (N).fv from (by exact fresh_y_not_N)))) (show y ∉ ((syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((syn_cplc (syn_ctfin M) (syn_ctfin (.cv x)))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cplc (syn_ctfin M) (syn_ctfin (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((syn_ctfin M)).fv) ∪ (((syn_ctfin (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))) (show y ∉ ((syn_ctfin (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0053
  have p0055 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (.classMem (syn_ctfin (.cv x)) (syn_cnnc)) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) p0037 p0050 p0054
  have p0056 :=
    @g_n_3expa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) p0055
  have p0057 :=
    @g_exp32 (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))) (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) p0056
  have p0058 :=
    @g_com12 (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))) (syn_wne N (syn_c0)) (.imp (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))) p0057
  have p0059 :=
    @g_pm2_61ine (.imp (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))) (.imp (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))))) N (syn_c0) p0024 p0058
  have p0060 :=
    @g_expr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)) (.imp (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))) p0059
  have p0061 :=
    @g_rexlimdv (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wne M (syn_c0))) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) x (syn_cnnc) (by exact (show x ∉ ((syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show x ∉ ((((syn_cnnc)).fv).erase y) ∪ ((((Wff.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))).fv).erase y) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (((syn_cnnc)).fv).erase y from (fun hmem => (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show x ∉ (((Wff.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))).fv).erase y from (fun hmem => (show x ∉ ((Wff.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_ctfin N)).fv) ∪ (((syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show x ∉ (N).fv from (by exact fresh_x_not_N)))) (show x ∉ ((syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((syn_cplc (syn_ctfin M) (.cv y))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cplc (syn_ctfin M) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((syn_ctfin M)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show x ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wne M (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv) ∪ (((syn_wne M (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (M).fv from (by exact fresh_x_not_M)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (N).fv from (by exact fresh_x_not_N)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show x ∉ ((syn_wne M (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show x ∉ ((M).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (M).fv from (by exact fresh_x_not_M)) (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0060
  have p0062 :=
    @g_ex (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wne M (syn_c0)) (.imp (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))) p0061
  have p0063 :=
    @g_imp3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wne M (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) p0062
  have p0064 :=
    @g_jcad (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))) p0003 p0063
  have p0065 :=
    @g_opkltfing x M N (syn_cnnc) (syn_cnnc) (by exact (show x ∉ (M).fv from (by exact fresh_x_not_M))) (by exact (show x ∉ (N).fv from (by exact fresh_x_not_N)))
  have p0066 :=
    @g_tfinex M
  have p0067 :=
    @g_tfinex N
  have p0068 :=
    @g_opkltfing y (syn_ctfin M) (syn_ctfin N) (syn_cvv) (syn_cvv) (by exact (show y ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show y ∉ (M).fv from (by exact fresh_y_not_M))))) (by exact (show y ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show y ∉ (N).fv from (by exact fresh_y_not_N)))))
  have p0069 :=
    @g_mp2an (.classMem (syn_ctfin M) (syn_cvv)) (.classMem (syn_ctfin N) (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))))) p0066 p0067 p0068
  have p0070 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))))) (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) p0069
  have p0071 :=
    @g_n_3imtr4d (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (syn_wne M (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))) (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))) (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0064 p0065 p0070
  exact p0071

noncomputable def g_tfinltfin
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wb (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_tfinltfinlem1 M N
  have p0001 :=
    @g_tfineq M (syn_c0)
  have p0002 :=
    @g_tfinnul
  have p0003 :=
    @g_syl6eq (.classEq M (syn_c0)) (syn_ctfin M) (syn_ctfin (syn_c0)) (syn_c0) p0001 p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_ctfin M) (syn_c0))))
  have p0005 :=
    @g_con2bii (syn_wne (syn_ctfin M) (syn_c0)) (.classEq (syn_ctfin M) (syn_c0)) p0004
  have p0006 :=
    @g_sylib (.classEq M (syn_c0)) (.classEq (syn_ctfin M) (syn_c0)) (.neg (syn_wne (syn_ctfin M) (syn_c0))) p0003 p0005
  have p0007 :=
    @g_intnanrd (.classEq M (syn_c0)) (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv x)) (syn_c1c)))) p0006
  have p0008 :=
    @g_tfinex M
  have p0009 :=
    @g_tfinex N
  have p0010 :=
    @g_opkltfing x (syn_ctfin M) (syn_ctfin N) (syn_cvv) (syn_cvv) (by exact (show x ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show x ∉ (M).fv from (by exact fresh_x_not_M))))) (by exact (show x ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show x ∉ (N).fv from (by exact fresh_x_not_N)))))
  have p0011 :=
    @g_mp2an (.classMem (syn_ctfin M) (syn_cvv)) (.classMem (syn_ctfin N) (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv x)) (syn_c1c)))))) p0008 p0009 p0010
  have p0012 :=
    @g_sylnibr (.classEq M (syn_c0)) (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv x)) (syn_c1c))))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0007 p0011
  have p0013 :=
    @g_pm2_21d (.classEq M (syn_c0)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk M N) (syn_cltfin)) p0012
  have p0014 :=
    @g_a1d (.classEq M (syn_c0)) (.imp (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk M N) (syn_cltfin))) (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) p0013
  have p0015 :=
    @g_tfinprop M y (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
  have p0016 :=
    @g_simpld (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex y M (.classMem (syn_cpw1 (.cv y)) (syn_ctfin M))) p0015
  have p0017 :=
    @g_ltfinirr (syn_ctfin M)
  have p0018 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_ctfin M) (syn_cnnc)) (.neg (.classMem (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_cltfin))) p0016 p0017
  have p0019 :=
    @g_n_3adant2 (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (.neg (.classMem (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_cltfin))) (.classMem N (syn_cnnc)) p0018
  have p0020 :=
    @g_opkeq2 (syn_ctfin M) (syn_ctfin N) (syn_ctfin M)
  have p0021 :=
    @g_eleq1d (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin) p0020
  have p0022 :=
    @g_notbid (.classEq (syn_ctfin M) (syn_ctfin N)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_cltfin)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0021
  have p0023 :=
    @g_syl5ibcom (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.neg (.classMem (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_cltfin))) (.classEq (syn_ctfin M) (syn_ctfin N)) (.neg (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))) p0019 p0022
  have p0024 :=
    @g_con2d (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classEq (syn_ctfin M) (syn_ctfin N)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0023
  have p0025 :=
    @g_imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.neg (.classEq (syn_ctfin M) (syn_ctfin N))) p0024
  have p0026 :=
    @g_tfineq M N
  have p0027 :=
    @g_nsyl (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))) (.classEq (syn_ctfin M) (syn_ctfin N)) (.classEq M N) p0025 p0026
  have p0028 :=
    @g_simpl1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0)))
  have p0029 :=
    @g_simpl3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0)))
  have p0030 :=
    @g_syl2anc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0)))) (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_cnnc)) p0028 p0029 p0016
  have p0031 :=
    @g_simpl2 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0)))
  have p0032 :=
    @g_simprr (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0))
  have p0033 :=
    @g_tfinprop N y (by exact (show y ∉ (N).fv from (by exact fresh_y_not_N)))
  have p0034 :=
    @g_simpld (syn_wa (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wrex y N (.classMem (syn_cpw1 (.cv y)) (syn_ctfin N))) p0033
  have p0035 :=
    @g_syl2anc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0)))) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) (.classMem (syn_ctfin N) (syn_cnnc)) p0031 p0032 p0034
  have p0036 :=
    @g_jca (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0)))) (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) p0030 p0035
  have p0037 :=
    @g_simprl (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0))
  have p0038 :=
    @g_ltfinasym (syn_ctfin M) (syn_ctfin N)
  have p0039 :=
    @g_sylc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0)))) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))) p0036 p0037 p0038
  have p0040 :=
    @g_expr (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0)) (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))) p0039
  have p0041 :=
    @g_imnan (syn_wne N (syn_c0)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))
  have p0042 :=
    @g_sylib (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))) (.imp (syn_wne N (syn_c0)) (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)))) (.neg (syn_wa (syn_wne N (syn_c0)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)))) p0040 p0041
  have p0043 :=
    @g_opkltfing y N M (syn_cnnc) (syn_cnnc) (by exact (show y ∉ (N).fv from (by exact fresh_y_not_N))) (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
  have p0044 :=
    @g_ancoms (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc)) (syn_wb (.classMem (syn_copk N M) (syn_cltfin)) (syn_wa (syn_wne N (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq M (syn_cplc (syn_cplc N (.cv y)) (syn_c1c)))))) p0043
  have p0045 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wb (.classMem (syn_copk N M) (syn_cltfin)) (syn_wa (syn_wne N (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq M (syn_cplc (syn_cplc N (.cv y)) (syn_c1c)))))) (syn_wne M (syn_c0)) p0044
  have p0046 :=
    @g_simprbda (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk N M) (syn_cltfin)) (syn_wne N (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq M (syn_cplc (syn_cplc N (.cv y)) (syn_c1c)))) p0045
  have p0047 :=
    @g_adantrl (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk N M) (syn_cltfin)) (syn_wne N (syn_c0)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0046
  have p0048 :=
    @g_simpl2 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)))
  have p0049 :=
    @g_simpl1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)))
  have p0050 :=
    @g_jca (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)))) (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc)) p0048 p0049
  have p0051 :=
    @g_simprr (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin))
  have p0052 :=
    @g_tfinltfinlem1 N M
  have p0053 :=
    @g_sylc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)))) (syn_wa (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc))) (.classMem (syn_copk N M) (syn_cltfin)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)) p0050 p0051 p0052
  have p0054 :=
    @g_jca (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)))) (syn_wne N (syn_c0)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)) p0047 p0053
  have p0055 :=
    @g_expr (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)) (syn_wa (syn_wne N (syn_c0)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))) p0054
  have p0056 :=
    @g_mtod (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))) (.classMem (syn_copk N M) (syn_cltfin)) (syn_wa (syn_wne N (syn_c0)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))) p0042 p0055
  have p0057 :=
    @g_ltfintri M N
  have p0058 :=
    @g_adantr (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0057
  have p0059 :=
    @g_ecase23d (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))) (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin)) p0027 p0056 p0058
  have p0060 :=
    @g_ex (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk M N) (syn_cltfin)) p0059
  have p0061 :=
    @g_n_3expa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)) (.imp (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk M N) (syn_cltfin))) p0060
  have p0062 :=
    @g_expcom (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wne M (syn_c0)) (.imp (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk M N) (syn_cltfin))) p0061
  have p0063 :=
    @g_pm2_61ine (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.imp (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (.classMem (syn_copk M N) (syn_cltfin)))) M (syn_c0) p0014 p0062
  have p0064 :=
    @g_impbid (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (syn_copk M N) (syn_cltfin)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0000 p0063
  exact p0064

noncomputable def g_tfinlefin
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wb (.classMem (syn_copk M N) (syn_clefin)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  have p0000 :=
    @g_tfinltfin N M
  have p0001 :=
    @g_ancoms (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc)) (syn_wb (.classMem (syn_copk N M) (syn_cltfin)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))) p0000
  have p0002 :=
    @g_notbid (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (syn_copk N M) (syn_cltfin)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)) p0001
  have p0003 :=
    @g_lenltfin M N
  have p0004 :=
    @g_tfincl M
  have p0005 :=
    @g_tfincl N
  have p0006 :=
    @g_lenltfin (syn_ctfin M) (syn_ctfin N)
  have p0007 :=
    @g_syl2an (.classMem M (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wb (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)) (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)))) (.classMem N (syn_cnnc)) p0004 p0005 p0006
  have p0008 :=
    @g_n_3bitr4d (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.neg (.classMem (syn_copk N M) (syn_cltfin))) (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))) (.classMem (syn_copk M N) (syn_clefin)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)) p0002 p0003 p0007
  exact p0008



#print axioms g_tfinlefin

end NFChoice.DirectNominalPrf.WPPReplay
