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
import NominalWPPReplayChunk009StructuralPart046


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

noncomputable def g_vfinnc
    (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) (syn_wreu x (syn_cnnc) (.classMem A (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_ssv A
  have p0001 :=
    @g_ssfin A (syn_cvv) V
  have p0002 :=
    @g_mp3an3 (.classMem A V) (.classMem (syn_cvv) (syn_cfin)) (syn_wss A (syn_cvv)) (.classMem A (syn_cfin)) p0000 p0001
  have p0003 :=
    @g_elfin x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0004 :=
    @g_sylib (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) (.classMem A (syn_cfin)) (syn_wrex x (syn_cnnc) (.classMem A (.cv x))) p0002 p0003
  have p0005 :=
    @g_nnceleq A (.cv x) (.cv y)
  have p0006_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0005
  have p0006 :=
    @g_ex (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y) p0006_e00_recanon
  have p0007 :=
    @g_rgen2a (.imp (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y)) x y (syn_cnnc) (by exact (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) p0006
  have p0008 :=
    @g_a1i (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (.imp (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y)))) (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) p0007
  have p0009 :=
    @g_eleq2 (.cv x) (.cv y) A
  have p0010_e00_recanon : Nominal.NPrf (.imp (.objEq x y) (syn_wb (.classMem A (.cv x)) (.classMem A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_reu4 (.classMem A (.cv x)) (.classMem A (.cv y)) x y (syn_cnnc) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((Wff.classMem A (.cv x))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))) (by exact (show x ∉ ((Wff.classMem A (.cv y))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y))))))))))) (show x ≠ y from (by exact fresh_x_ne_y)) p0010_e00_recanon
  have p0011 :=
    @g_sylanbrc (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) (syn_wrex x (syn_cnnc) (.classMem A (.cv x))) (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (.imp (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y)))) (syn_wreu x (syn_cnnc) (.classMem A (.cv x))) p0004 p0008 p0010
  exact p0011

noncomputable def g_ncfinex
    (A : Class) :
    Nominal.NPrf (.classMem (syn_cncfin A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ncfin x A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0001 :=
    @g_iotaex (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x))) x
  have p0002 :=
    @g_eqeltri (syn_cncfin A) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) (syn_cvv) p0000 p0001
  exact p0002

noncomputable def g_ncfineq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cncfin A) (syn_cncfin B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eleq1 A B (.cv x)
  have p0001 :=
    @g_anbi2d (.classEq A B) (.classMem A (.cv x)) (.classMem B (.cv x)) (.classMem (.cv x) (syn_cnnc)) p0000
  have p0002 :=
    @g_iotabidv (.classEq A B) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem B (.cv x))) x (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ncfin x A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ncfin x B (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem B (.cv x)))) (syn_cncfin A) (syn_cncfin B) p0002 p0003 p0004
  exact p0005

noncomputable def g_ncfinprop
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (syn_wa (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ncfin x A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0001 :=
    @g_vfinnc x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0002 :=
    @g_reiotacl (.classMem A (.cv x)) x (syn_cnnc) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0003 :=
    @g_syl (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) (syn_wreu x (syn_cnnc) (.classMem A (.cv x))) (.classMem (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) (syn_cncfin A) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) (syn_cnnc) p0000 p0003
  have p0005 :=
    @g_eqcomi (syn_cncfin A) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) p0000
  have p0006 :=
    @g_eleq2 (.cv x) (syn_cncfin A) A
  have p0007 :=
    @g_reiota2 (.classMem A (.cv x)) (.classMem A (syn_cncfin A)) x (syn_cnnc) (syn_cncfin A) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_cncfin A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show x ∉ ((Wff.classMem A (syn_cncfin A))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cncfin A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cncfin A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))))))) p0006
  have p0008 :=
    @g_syl2anc (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) (.classMem (syn_cncfin A) (syn_cnnc)) (syn_wreu x (syn_cnnc) (.classMem A (.cv x))) (syn_wb (.classMem A (syn_cncfin A)) (.classEq (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) (syn_cncfin A))) p0004 p0001 p0007
  have p0009 :=
    @g_mpbiri (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) (.classMem A (syn_cncfin A)) (.classEq (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) (syn_cncfin A)) p0005 p0008
  have p0010 :=
    @g_jca (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)) p0004 p0009
  have p0011 :=
    @g_ancoms (.classMem A V) (.classMem (syn_cvv) (syn_cfin)) (syn_wa (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A))) p0010
  exact p0011

noncomputable def g_ncfindi
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classEq (syn_cncfin (syn_cun A B)) (syn_cplc (syn_cncfin A) (syn_cncfin B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_simp1l (.classMem (syn_cvv) (syn_cfin)) (.classMem A V) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))
  have p0001 :=
    @g_simp1r (.classMem (syn_cvv) (syn_cfin)) (.classMem A V) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))
  have p0002 :=
    @g_simp2 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))
  have p0003 :=
    @g_unexg A B V W
  have p0004 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem A V) (.classMem B W) (.classMem (syn_cun A B) (syn_cvv)) p0001 p0002 p0003
  have p0005 :=
    @g_ncfinprop (syn_cun A B) (syn_cvv)
  have p0006 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cun A B) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_cun A B)) (syn_cnnc)) (.classMem (syn_cun A B) (syn_cncfin (syn_cun A B)))) p0000 p0004 p0005
  have p0007 :=
    @g_simpld (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cncfin (syn_cun A B)) (syn_cnnc)) (.classMem (syn_cun A B) (syn_cncfin (syn_cun A B))) p0006
  have p0008 :=
    @g_ncfinprop A V
  have p0009 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cvv) (syn_cfin)) (.classMem A V) (syn_wa (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A))) p0000 p0001 p0008
  have p0010 :=
    @g_simpld (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)) p0009
  have p0011 :=
    @g_ncfinprop B W
  have p0012 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cvv) (syn_cfin)) (.classMem B W) (syn_wa (.classMem (syn_cncfin B) (syn_cnnc)) (.classMem B (syn_cncfin B))) p0000 p0002 p0011
  have p0013 :=
    @g_simpld (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cncfin B) (syn_cnnc)) (.classMem B (syn_cncfin B)) p0012
  have p0014 :=
    @g_nncaddccl (syn_cncfin A) (syn_cncfin B)
  have p0015 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem (syn_cncfin B) (syn_cnnc)) (.classMem (syn_cplc (syn_cncfin A) (syn_cncfin B)) (syn_cnnc)) p0010 p0013 p0014
  have p0016 :=
    @g_simprd (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cncfin (syn_cun A B)) (syn_cnnc)) (.classMem (syn_cun A B) (syn_cncfin (syn_cun A B))) p0006
  have p0017 :=
    @g_simprd (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)) p0009
  have p0018 :=
    @g_simprd (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cncfin B) (syn_cnnc)) (.classMem B (syn_cncfin B)) p0012
  have p0019 :=
    @g_simp3 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))
  have p0020 :=
    @g_eladdci A B (syn_cncfin A) (syn_cncfin B)
  have p0021 :=
    @g_syl3anc (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem A (syn_cncfin A)) (.classMem B (syn_cncfin B)) (.classEq (syn_cin A B) (syn_c0)) (.classMem (syn_cun A B) (syn_cplc (syn_cncfin A) (syn_cncfin B))) p0017 p0018 p0019 p0020
  have p0022 :=
    @g_nnceleq (syn_cun A B) (syn_cncfin (syn_cun A B)) (syn_cplc (syn_cncfin A) (syn_cncfin B))
  have p0023 :=
    @g_syl22anc (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cncfin (syn_cun A B)) (syn_cnnc)) (.classMem (syn_cplc (syn_cncfin A) (syn_cncfin B)) (syn_cnnc)) (.classMem (syn_cun A B) (syn_cncfin (syn_cun A B))) (.classMem (syn_cun A B) (syn_cplc (syn_cncfin A) (syn_cncfin B))) (.classEq (syn_cncfin (syn_cun A B)) (syn_cplc (syn_cncfin A) (syn_cncfin B))) p0007 p0015 p0016 p0021 p0022
  exact p0023

noncomputable def g_ncfinsn
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classEq (syn_cncfin (syn_csn A)) (syn_c1c))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_snex A
  have p0001 :=
    @g_ncfinprop (syn_csn A) (syn_cvv)
  have p0002 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_csn A) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc)) (.classMem (syn_csn A) (syn_cncfin (syn_csn A)))) p0000 p0001
  have p0003 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin)) (syn_wa (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc)) (.classMem (syn_csn A) (syn_cncfin (syn_csn A)))) (.classMem A V) p0002
  have p0004 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc)) (.classMem (syn_csn A) (syn_cncfin (syn_csn A))) p0003
  have p0005 :=
    @g_n_1cnnc
  have p0006 :=
    @g_a1i (.classMem (syn_c1c) (syn_cnnc)) (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) p0005
  have p0007 :=
    @g_simprd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc)) (.classMem (syn_csn A) (syn_cncfin (syn_csn A))) p0003
  have p0008 :=
    @g_snel1cg A V
  have p0009 :=
    @g_adantl (.classMem A V) (.classMem (syn_csn A) (syn_c1c)) (.classMem (syn_cvv) (syn_cfin)) p0008
  have p0010 :=
    @g_nnceleq (syn_csn A) (syn_cncfin (syn_csn A)) (syn_c1c)
  have p0011 :=
    @g_syl22anc (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cnnc)) (.classMem (syn_csn A) (syn_cncfin (syn_csn A))) (.classMem (syn_csn A) (syn_c1c)) (.classEq (syn_cncfin (syn_csn A)) (syn_c1c)) p0004 p0006 p0007 p0009 p0010
  exact p0011

noncomputable def g_eqpwrelk
    (A : Class) (B : Class) (hyp_eqpwrelk_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_eqpwrelk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq B (syn_cpw A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have p0000 :=
    @g_opkex (syn_csn A) B
  have p0001 :=
    @g_elimak t (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (syn_csn A) B) (by exact (show t ∉ ((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show t ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ (((syn_cins3k (syn_csik (syn_cssetk)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show t ∉ ((syn_csik (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show t ∉ ((syn_copk (syn_csn A) B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((syn_csn A)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))) (show t ∉ (B).fv from (by exact fresh_t_not_B))))))) p0000
  have p0002 :=
    @g_elpw121c x (.cv t) (by exact (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))))
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))) x (by exact (show x ∉ ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk (.cv t) (syn_copk (syn_csn A) B))).fv) ∪ (((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk (.cv t) (syn_copk (syn_csn A) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv t)).fv) ∪ (((syn_copk (syn_csn A) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))) (show x ∉ ((syn_copk (syn_csn A) B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((syn_csn A)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ (B).fv from (by exact fresh_x_not_B)))))))))) (show x ∉ ((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show x ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ (((syn_cins3k (syn_csik (syn_cssetk)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show x ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ ((syn_csik (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))) (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))) t p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))))
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))) x t
  have p0009 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))) (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))))) p0006 p0007 p0008
  have p0010 :=
    @g_snex (syn_csn (syn_csn (.cv x)))
  have p0011 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)
  have p0012 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))) p0011
  have p0013 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))) t (syn_csn (syn_csn (syn_csn (.cv x)))) (by exact (show t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))))))) (by exact (show t ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))).fv) ∪ (((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((syn_csn (syn_csn (syn_csn (.cv x))))).fv) ∪ (((syn_copk (syn_csn A) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))))))))) (show t ∉ ((syn_copk (syn_csn A) B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((syn_csn A)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))) (show t ∉ (B).fv from (by exact fresh_t_not_B)))))))))) (show t ∉ ((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show t ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ (((syn_cins3k (syn_csik (syn_cssetk)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show t ∉ ((syn_csik (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0010 p0012
  have p0014 :=
    @g_elsymdif (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))
  have p0015 :=
    @g_snex (.cv x)
  have p0016 :=
    @g_snex A
  have p0017 :=
    @g_otkelins2k (syn_csn (.cv x)) (syn_csn A) B (syn_cssetk) p0015 p0016 hyp_eqpwrelk_2
  have p0018 :=
    @g_vex x
  have p0019 :=
    @g_elssetk (.cv x) B p0018 hyp_eqpwrelk_2
  have p0020 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0017 p0019
  have p0021 :=
    @g_otkelins3k (syn_csn (.cv x)) (syn_csn A) B (syn_csik (syn_cssetk)) p0015 p0016 hyp_eqpwrelk_2
  have p0022 :=
    @g_opksnelsik (.cv x) A (syn_cssetk) p0018 hyp_eqpwrelk_1
  have p0023 :=
    @g_opkelssetkg (.cv x) A (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem A (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv x) A) (syn_cssetk)) (syn_wss (.cv x) A)) p0018 hyp_eqpwrelk_1 p0023
  have p0025 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins3k (syn_csik (syn_cssetk)))) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn A)) (syn_csik (syn_cssetk))) (.classMem (syn_copk (.cv x) A) (syn_cssetk)) (syn_wss (.cv x) A) p0021 p0022 p0024
  have p0026 :=
    @g_bibi12i (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins2k (syn_cssetk))) (.classMem (.cv x) B) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins3k (syn_csik (syn_cssetk)))) (syn_wss (.cv x) A) p0020 p0025
  have p0027 :=
    @g_notbii (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins3k (syn_csik (syn_cssetk))))) (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)) p0026
  have p0028 :=
    @g_n_3bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))) (.neg (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins3k (syn_csik (syn_cssetk)))))) (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A))) p0013 p0014 p0027
  have p0029 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))) (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A))) x p0028
  have p0030 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn A) B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))))) (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)))) p0001 p0009 p0029
  have p0031 :=
    @g_notbii (.classMem (syn_copk (syn_csn A) B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)))) p0030
  have p0032 :=
    @g_elcompl (syn_copk (syn_csn A) B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0000
  have p0033 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0034 :=
    @g_eqeq2i (syn_cpw A) (.cab x (syn_wss (.cv x) A)) B p0033
  have p0035 :=
    @g_eqabb (syn_wss (.cv x) A) x B (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0036 :=
    @g_alex (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)) x
  have p0037 :=
    @g_n_3bitri (.classEq B (syn_cpw A)) (.classEq B (.cab x (syn_wss (.cv x) A))) (.all x (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A))) (.neg (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A))))) p0034 p0035 p0036
  have p0038 :=
    @g_n_3bitr4i (.neg (.classMem (syn_copk (syn_csn A) B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.neg (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A))))) (.classMem (syn_copk (syn_csn A) B) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq B (syn_cpw A)) p0031 p0032 p0037
  exact p0038

noncomputable def g_eqpw1relk
    (A : Class) (B : Class) (hyp_eqpw1relk_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_eqpw1relk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk A (syn_csn B)) (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_cpw1 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have p0000 :=
    @g_snex B
  have p0001 :=
    @g_opkelxpk A (syn_csn B) (syn_cpw (syn_c1c)) (syn_cvv) hyp_eqpw1relk_1 p0000
  have p0002 :=
    @g_mpbiran2 (.classMem (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))) (.classMem A (syn_cpw (syn_c1c))) (.classMem (syn_csn B) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_elpw A (syn_c1c) hyp_eqpw1relk_1
  have p0004 :=
    @g_bitri (.classMem (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))) (.classMem A (syn_cpw (syn_c1c))) (syn_wss A (syn_c1c)) p0002 p0003
  have p0005 :=
    @g_opkex A (syn_csn B)
  have p0006 :=
    @g_elimak t (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_copk A (syn_csn B)) (by exact (show t ∉ ((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show t ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_csik (syn_cssetk)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cins2k (syn_csik (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show t ∉ ((syn_csik (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) (by exact (show t ∉ ((syn_copk A (syn_csn B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ ((A).fv) ∪ (((syn_csn B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ (A).fv from (by exact fresh_t_not_A)) (show t ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ (B).fv from (by exact fresh_t_not_B))))))))) p0005
  have p0007 :=
    @g_elpw131c x (.cv t) (by exact (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))))
  have p0008 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) p0007
  have p0009 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) x (by exact (show x ∉ ((Wff.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk (.cv t) (syn_copk A (syn_csn B)))).fv) ∪ (((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk (.cv t) (syn_copk A (syn_csn B)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv t)).fv) ∪ (((syn_copk A (syn_csn B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))) (show x ∉ ((syn_copk A (syn_csn B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((A).fv) ∪ (((syn_csn B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))))))))))) (show x ∉ ((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show x ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_csik (syn_cssetk)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show x ∉ ((syn_cins2k (syn_csik (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show x ∉ ((syn_csik (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))
  have p0010 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) p0008 p0009
  have p0011 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) t p0010
  have p0012 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))))
  have p0013 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) x t
  have p0014 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))) p0011 p0012 p0013
  have p0015 :=
    @g_bitri (.classMem (syn_copk A (syn_csn B)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))) p0006 p0014
  have p0016 :=
    @g_snex (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0017 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))
  have p0018 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) p0017
  have p0019 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) t (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (by exact (show t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))))))))) (by exact (show t ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B)))).fv) ∪ (((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv) ∪ (((syn_copk A (syn_csn B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))))))))))) (show t ∉ ((syn_copk A (syn_csn B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ ((A).fv) ∪ (((syn_csn B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ (A).fv from (by exact fresh_t_not_A)) (show t ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))))))))))) (show t ∉ ((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show t ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_csik (syn_cssetk)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cins2k (syn_csik (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show t ∉ ((syn_csik (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0016 p0018
  have p0020 :=
    @g_elsymdif (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))
  have p0021 :=
    @g_snex (syn_csn (.cv x))
  have p0022 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv x))) A (syn_csn B) (syn_cssetk) p0021 hyp_eqpw1relk_1 p0000
  have p0023 :=
    @g_snex (.cv x)
  have p0024 :=
    @g_elssetk (syn_csn (.cv x)) A p0023 hyp_eqpw1relk_1
  have p0025 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_cins3k (syn_cssetk))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) A) (syn_cssetk)) (.classMem (syn_csn (.cv x)) A) p0022 p0024
  have p0026 :=
    @g_otkelins2k (syn_csn (syn_csn (.cv x))) A (syn_csn B) (syn_csik (syn_cssetk)) p0021 hyp_eqpw1relk_1 p0000
  have p0027 :=
    @g_opksnelsik (syn_csn (.cv x)) B (syn_cssetk) p0023 hyp_eqpw1relk_2
  have p0028 :=
    @g_vex x
  have p0029 :=
    @g_elssetk (.cv x) B p0028 hyp_eqpw1relk_2
  have p0030 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn B)) (syn_csik (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0027 p0029
  have p0031 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_cins2k (syn_csik (syn_cssetk)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn B)) (syn_csik (syn_cssetk))) (.classMem (.cv x) B) p0026 p0030
  have p0032 :=
    @g_bibi12i (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_cins3k (syn_cssetk))) (.classMem (syn_csn (.cv x)) A) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_cins2k (syn_csik (syn_cssetk)))) (.classMem (.cv x) B) p0025 p0031
  have p0033 :=
    @g_xchbinx (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_cins3k (syn_cssetk))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_cins2k (syn_csik (syn_cssetk))))) (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)) p0020 p0032
  have p0034 :=
    @g_bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) (.neg (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0019 p0033
  have p0035 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) (.neg (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) x p0034
  have p0036 :=
    @g_exnal (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)) x
  have p0037 :=
    @g_n_3bitrri (.classMem (syn_copk A (syn_csn B)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))) (syn_wex x (.neg (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)))) (.neg (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)))) p0015 p0035 p0036
  have p0038 :=
    @g_con1bii (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) (.classMem (syn_copk A (syn_csn B)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0037
  have p0039 :=
    @g_anbi12i (.classMem (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))) (syn_wss A (syn_c1c)) (.neg (.classMem (syn_copk A (syn_csn B)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0004 p0038
  have p0040 :=
    @g_eldif (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0041 :=
    @g_eqpw1 x A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0042 :=
    @g_n_3bitr4i (syn_wa (.classMem (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))) (.neg (.classMem (syn_copk A (syn_csn B)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wa (syn_wss A (syn_c1c)) (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)))) (.classMem (syn_copk A (syn_csn B)) (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_cpw1 B)) p0039 p0040 p0041
  exact p0042



#print axioms g_eqpw1relk

end NFChoice.DirectNominalPrf.WPPReplay
