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
import NominalWPPReplayChunk009StructuralPart059


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

noncomputable def g_n_0ceven
     :
    Nominal.NPrf (.classMem (syn_c0c) (syn_cevenfin)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have p0000 :=
    @g_peano1
  have p0001 :=
    @g_addcid2 (syn_c0c)
  have p0002 :=
    @g_eqcomi (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c) p0001
  have p0003 :=
    @g_addceq12 (.cv n) (.cv n) (syn_c0c) (syn_c0c)
  have p0004 :=
    @g_anidms (.classEq (.cv n) (syn_c0c)) (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c0c) (syn_c0c))) p0003
  have p0005 :=
    @g_eqeq2d (.classEq (.cv n) (syn_c0c)) (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c) p0004
  have p0006 :=
    @g_rspcev (.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n))) (.classEq (syn_c0c) (syn_cplc (syn_c0c) (syn_c0c))) n (syn_c0c) (syn_cnnc) (by exact (show n ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((Wff.classEq (syn_c0c) (syn_cplc (syn_c0c) (syn_c0c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((syn_c0c)).fv) ∪ (((syn_cplc (syn_c0c) (syn_c0c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show n ∉ ((syn_cplc (syn_c0c) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show n ∉ (((syn_c0c)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show n ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0005
  have p0007 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classEq (syn_c0c) (syn_cplc (syn_c0c) (syn_c0c))) (syn_wrex n (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n)))) p0000 p0002 p0006
  have p0008 :=
    @g_n_0ex
  have p0009 :=
    @g_snid (syn_c0) p0008
  have p0010 :=
    (by simpa [syn_c0c] using (Nominal.classEqRefl (syn_c0c)))
  have p0011 :=
    @g_eleqtrri (syn_c0) (syn_csn (syn_c0)) (syn_c0c) p0009 p0010
  have p0012 :=
    @g_ne0i (syn_c0c) (syn_c0)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_n_0cex
  have p0015 :=
    @g_eqeq1 (.cv x) (syn_c0c) (syn_cplc (.cv n) (.cv n))
  have p0016 :=
    @g_rexbidv (.classEq (.cv x) (syn_c0c)) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n))) n (syn_cnnc) (by exact (show n ∉ ((Wff.classEq (.cv x) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((Class.cv x)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ x from (by exact fresh_n_ne_x)))))) (show n ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0015
  have p0017 :=
    @g_neeq1 (.cv x) (syn_c0c) (syn_c0)
  have p0018 :=
    @g_anbi12d (.classEq (.cv x) (syn_c0c)) (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_c0c) (syn_c0)) p0016 p0017
  have p0019 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x n (show n ≠ x from (by exact fresh_n_ne_x))
  have p0020 :=
    @g_elab2 (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex n (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n)))) (syn_wne (syn_c0c) (syn_c0))) x (syn_c0c) (syn_cevenfin) (by exact (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_wa (syn_wrex n (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n)))) (syn_wne (syn_c0c) (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((syn_wrex n (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n))))).fv) ∪ (((syn_wne (syn_c0c) (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wrex n (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show x ∉ ((((syn_cnnc)).fv).erase n) ∪ ((((Wff.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n)))).fv).erase n) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (((syn_cnnc)).fv).erase n from (fun hmem => (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show x ∉ (((Wff.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n)))).fv).erase n from (fun hmem => (show x ∉ ((Wff.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_c0c)).fv) ∪ (((syn_cplc (.cv n) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_cplc (.cv n) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv n)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ n from (by exact fresh_x_ne_n)))))) (show x ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ n from (by exact fresh_x_ne_n)))))))))))))) (Finset.mem_of_mem_erase hmem))))))) (show x ∉ ((syn_wne (syn_c0c) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show x ∉ (((syn_c0c)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0014 p0018 p0019
  have p0021 :=
    @g_mpbir2an (.classMem (syn_c0c) (syn_cevenfin)) (syn_wrex n (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv n) (.cv n)))) (syn_wne (syn_c0c) (syn_c0)) p0007 p0013 p0020
  exact p0021

noncomputable def g_evennn
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cevenfin)) (.classMem A (syn_cnnc))) := by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have p0000 :=
    @g_eqeq1 (.cv x) A (syn_cplc (.cv n) (.cv n))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (.classEq A (syn_cplc (.cv n) (.cv n))) n (syn_cnnc) (by exact (show n ∉ ((Wff.classEq (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ x from (by exact fresh_n_ne_x)))))) (show n ∉ (A).fv from (by exact fresh_n_not_A))))))) p0000
  have p0002 :=
    @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x n (show n ≠ x from (by exact fresh_n_ne_x))
  have p0005 :=
    @g_elab2g (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne A (syn_c0))) x A (syn_cevenfin) (syn_cevenfin) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne A (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n))))).fv) ∪ (((syn_wne A (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show x ∉ ((((syn_cnnc)).fv).erase n) ∪ ((((Wff.classEq A (syn_cplc (.cv n) (.cv n)))).fv).erase n) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (((syn_cnnc)).fv).erase n from (fun hmem => (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show x ∉ (((Wff.classEq A (syn_cplc (.cv n) (.cv n)))).fv).erase n from (fun hmem => (show x ∉ ((Wff.classEq A (syn_cplc (.cv n) (.cv n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((syn_cplc (.cv n) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cplc (.cv n) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv n)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ n from (by exact fresh_x_ne_n)))))) (show x ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ n from (by exact fresh_x_ne_n)))))))))))))) (Finset.mem_of_mem_erase hmem))))))) (show x ∉ ((syn_wne A (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show x ∉ ((A).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_cevenfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne A (syn_c0))) p0005
  have p0007 :=
    @g_nncaddccl (.cv n) (.cv n)
  have p0008 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0007
  have p0009 :=
    @g_eleq1a (syn_cplc (.cv n) (.cv n)) (syn_cnnc) A
  have p0010 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.imp (.classEq A (syn_cplc (.cv n) (.cv n))) (.classMem A (syn_cnnc))) p0008 p0009
  have p0011 :=
    @g_rexlimiv (.classEq A (syn_cplc (.cv n) (.cv n))) (.classMem A (syn_cnnc)) n (syn_cnnc) (by exact (show n ∉ ((Wff.classMem A (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ ((A).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (A).fv from (by exact fresh_n_not_A)) (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0010
  have p0012 :=
    @g_adantr (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)) p0011
  have p0013 :=
    @g_syl (.classMem A (syn_cevenfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne A (syn_c0))) (.classMem A (syn_cnnc)) p0006 p0012
  exact p0013

#print axioms g_evennn

end NFChoice.DirectNominalPrf.WPPReplay
