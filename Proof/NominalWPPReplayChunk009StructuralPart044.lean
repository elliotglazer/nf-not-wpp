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
import NominalWPPReplayChunk009StructuralPart043


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

noncomputable def g_ltfintri
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin)))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (h))
  have fresh_k_not_N : k ∉ N.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (h))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_n_ne_k : n ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_n : k ≠ n :=
    Ne.symm fresh_n_ne_k
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_ne_p : n ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_n : p ≠ n :=
    Ne.symm fresh_n_ne_p
  have fresh_k_ne_m : k ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_k : m ≠ k :=
    Ne.symm fresh_k_ne_m
  have fresh_k_ne_p : k ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_k : p ≠ k :=
    Ne.symm fresh_k_ne_p
  have fresh_m_ne_p : m ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_m : p ≠ m :=
    Ne.symm fresh_m_ne_p
  have p0000 :=
    @g_opkeq2 (.cv n) N M
  have p0001 :=
    @g_eleq1d (.classEq (.cv n) N) (syn_copk M (.cv n)) (syn_copk M N) (syn_cltfin) p0000
  have p0002 :=
    @g_eqeq2 (.cv n) N M
  have p0003 :=
    @g_opkeq1 (.cv n) N M
  have p0004 :=
    @g_eleq1d (.classEq (.cv n) N) (syn_copk (.cv n) M) (syn_copk N M) (syn_cltfin) p0003
  have p0005 :=
    @g_n_3orbi123d (.classEq (.cv n) N) (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M (.cv n)) (.classEq M N) (.classMem (syn_copk (.cv n) M) (syn_cltfin)) (.classMem (syn_copk N M) (syn_cltfin)) p0001 p0002 p0004
  have p0006 :=
    @g_imbi2d (.classEq (.cv n) N) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin))) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin))) (syn_wne M (syn_c0)) p0005
  have p0007 :=
    @g_imbi2d (.classEq (.cv n) N) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin)))) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin)))) (.classMem M (syn_cnnc)) p0006
  have p0008 :=
    @g_ltfintrilem1 k n (show k ≠ n from (by exact fresh_k_ne_n))
  have p0009 :=
    @g_neeq1 (.cv k) (syn_c0c) (syn_c0)
  have p0010 :=
    @g_opkeq1 (.cv k) (syn_c0c) (.cv n)
  have p0011 :=
    @g_eleq1d (.classEq (.cv k) (syn_c0c)) (syn_copk (.cv k) (.cv n)) (syn_copk (syn_c0c) (.cv n)) (syn_cltfin) p0010
  have p0012 :=
    @g_eqeq1 (.cv k) (syn_c0c) (.cv n)
  have p0013 :=
    @g_opkeq2 (.cv k) (syn_c0c) (.cv n)
  have p0014 :=
    @g_eleq1d (.classEq (.cv k) (syn_c0c)) (syn_copk (.cv n) (.cv k)) (syn_copk (.cv n) (syn_c0c)) (syn_cltfin) p0013
  have p0015_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv k) (syn_c0c)) (syn_wb (.objEq k n) (.classEq (syn_c0c) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0012
  have p0015 :=
    @g_n_3orbi123d (.classEq (.cv k) (syn_c0c)) (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.objEq k n) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)) p0011 p0015_e01_recanon p0014
  have p0016 :=
    @g_imbi12d (.classEq (.cv k) (syn_c0c)) (syn_wne (.cv k) (syn_c0)) (syn_wne (syn_c0c) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))) (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))) p0009 p0015
  have p0017 :=
    @g_imbi2d (.classEq (.cv k) (syn_c0c)) (.imp (syn_wne (.cv k) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))) (.imp (syn_wne (syn_c0c) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))) (.classMem (.cv n) (syn_cnnc)) p0016
  have p0018 :=
    @g_neeq1 (.cv k) (.cv m) (syn_c0)
  have p0019 :=
    @g_opkeq1 (.cv k) (.cv m) (.cv n)
  have p0020_e00_recanon : Nominal.NPrf (.imp (.objEq k m) (.classEq (syn_copk (.cv k) (.cv n)) (syn_copk (.cv m) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0019
  have p0020 :=
    @g_eleq1d (.objEq k m) (syn_copk (.cv k) (.cv n)) (syn_copk (.cv m) (.cv n)) (syn_cltfin) p0020_e00_recanon
  have p0021 :=
    @g_eqeq1 (.cv k) (.cv m) (.cv n)
  have p0022 :=
    @g_opkeq2 (.cv k) (.cv m) (.cv n)
  have p0023_e00_recanon : Nominal.NPrf (.imp (.objEq k m) (.classEq (syn_copk (.cv n) (.cv k)) (syn_copk (.cv n) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0022
  have p0023 :=
    @g_eleq1d (.objEq k m) (syn_copk (.cv n) (.cv k)) (syn_copk (.cv n) (.cv m)) (syn_cltfin) p0023_e00_recanon
  have p0024_e01_recanon : Nominal.NPrf (.imp (.objEq k m) (syn_wb (.objEq k n) (.objEq m n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0021
  have p0024 :=
    @g_n_3orbi123d (.objEq k m) (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq k n) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) p0020 p0024_e01_recanon p0023
  have p0025_e00_recanon : Nominal.NPrf (.imp (.objEq k m) (syn_wb (syn_wne (.cv k) (syn_c0)) (syn_wne (.cv m) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0018
  have p0025 :=
    @g_imbi12d (.objEq k m) (syn_wne (.cv k) (syn_c0)) (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))) p0025_e00_recanon p0024
  have p0026 :=
    @g_imbi2d (.objEq k m) (.imp (syn_wne (.cv k) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) (.classMem (.cv n) (syn_cnnc)) p0025
  have p0027 :=
    @g_neeq1 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (syn_c0)
  have p0028 :=
    @g_opkeq1 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0029 :=
    @g_eleq1d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (syn_copk (.cv k) (.cv n)) (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin) p0028
  have p0030 :=
    @g_eqeq1 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0031 :=
    @g_opkeq2 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0032 :=
    @g_eleq1d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (syn_copk (.cv n) (.cv k)) (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin) p0031
  have p0033_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (syn_wb (.objEq k n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0030
  have p0033 :=
    @g_n_3orbi123d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.objEq k n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) p0029 p0033_e01_recanon p0032
  have p0034 :=
    @g_imbi12d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (syn_wne (.cv k) (syn_c0)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) p0027 p0033
  have p0035 :=
    @g_imbi2d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (.imp (syn_wne (.cv k) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))) (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))) (.classMem (.cv n) (syn_cnnc)) p0034
  have p0036 :=
    @g_neeq1 (.cv k) M (syn_c0)
  have p0037 :=
    @g_opkeq1 (.cv k) M (.cv n)
  have p0038 :=
    @g_eleq1d (.classEq (.cv k) M) (syn_copk (.cv k) (.cv n)) (syn_copk M (.cv n)) (syn_cltfin) p0037
  have p0039 :=
    @g_eqeq1 (.cv k) M (.cv n)
  have p0040 :=
    @g_opkeq2 (.cv k) M (.cv n)
  have p0041 :=
    @g_eleq1d (.classEq (.cv k) M) (syn_copk (.cv n) (.cv k)) (syn_copk (.cv n) M) (syn_cltfin) p0040
  have p0042_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv k) M) (syn_wb (.objEq k n) (.classEq M (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0039
  have p0042 :=
    @g_n_3orbi123d (.classEq (.cv k) M) (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.objEq k n) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)) (.classMem (syn_copk (.cv n) M) (syn_cltfin)) p0038 p0042_e01_recanon p0041
  have p0043 :=
    @g_imbi12d (.classEq (.cv k) M) (syn_wne (.cv k) (syn_c0)) (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin))) p0036 p0042
  have p0044 :=
    @g_imbi2d (.classEq (.cv k) M) (.imp (syn_wne (.cv k) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin)))) (.classMem (.cv n) (syn_cnnc)) p0043
  have p0045 :=
    @g_n_0cminle (.cv n)
  have p0046 :=
    @g_adantr (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_clefin)) (syn_wne (syn_c0c) (syn_c0)) p0045
  have p0047 :=
    @g_n_0cex
  have p0048 :=
    @g_lefinlteq (syn_c0c) (.cv n) (syn_cvv) (syn_cnnc)
  have p0049 :=
    @g_mp3an1 (.classMem (syn_c0c) (syn_cvv)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_c0c) (syn_c0)) (syn_wb (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_clefin)) (syn_wo (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)))) p0047 p0048
  have p0050 :=
    @g_orcom (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n))
  have p0051 :=
    @g_syl6bb (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_c0c) (syn_c0))) (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_clefin)) (syn_wo (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n))) (syn_wo (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))) p0049 p0050
  have p0052 :=
    @g_mpbid (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_c0c) (syn_c0))) (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_clefin)) (syn_wo (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))) p0046 p0051
  have p0053 :=
    @g_n_3mix2 (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))
  have p0054 :=
    @g_n_3mix1 (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))
  have p0055 :=
    @g_jaoi (.classEq (syn_c0c) (.cv n)) (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))) (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) p0053 p0054
  have p0056 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_c0c) (syn_c0))) (syn_wo (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))) (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))) p0052 p0055
  have p0057 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_c0c) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))) p0056
  have p0058 :=
    @g_addcnnul (.cv m) (syn_c1c)
  have p0059 :=
    @g_simpld (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_wne (.cv m) (syn_c0)) (syn_wne (syn_c1c) (syn_c0)) p0058
  have p0060 :=
    @g_n_3ad2ant3 (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (.classMem (.cv m) (syn_cnnc)) (syn_wne (.cv m) (syn_c0)) (.classMem (.cv n) (syn_cnnc)) p0059
  have p0061 :=
    @g_addc32 (.cv m) (.cv p) (syn_c1c)
  have p0062 :=
    @g_eqeq2i (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p)) (.cv n) p0061
  have p0063 :=
    @g_rexbii (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c))) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p))) p (syn_cnnc) p0062
  have p0064 :=
    @g_biimpi (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c)))) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p)))) p0063
  have p0065 :=
    @g_adantl (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c)))) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p)))) (syn_wne (.cv m) (syn_c0)) p0064
  have p0066 :=
    @g_a1i (.imp (syn_wa (syn_wne (.cv m) (syn_c0)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c))))) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p))))) (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) p0065
  have p0067 :=
    @g_opkltfing p (.cv m) (.cv n) (syn_cnnc) (syn_cnnc) (by exact (show p ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ m from (by exact fresh_p_ne_m))))))) (by exact (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))))
  have p0068 :=
    @g_n_3adant3 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (syn_wa (syn_wne (.cv m) (syn_c0)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0067
  have p0069 :=
    @g_simp1 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
  have p0070 :=
    @g_peano2 (.cv m)
  have p0071 :=
    @g_syl (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) p0069 p0070
  have p0072 :=
    @g_simp2 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
  have p0073 :=
    @g_opklefing p (syn_cplc (.cv m) (syn_c1c)) (.cv n) (syn_cnnc) (syn_cnnc) (by exact (show p ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show p ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ m from (by exact fresh_p_ne_m)))))) (show p ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))))
  have p0074 :=
    @g_syl2anc (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_clefin)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p))))) p0071 p0072 p0073
  have p0075 :=
    @g_n_3imtr4d (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (.cv m) (syn_c0)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c))))) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p)))) (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_clefin)) p0066 p0068 p0074
  have p0076 :=
    @g_lefinlteq (syn_cplc (.cv m) (syn_c1c)) (.cv n) (syn_cnnc) (syn_cnnc)
  have p0077 :=
    @g_syl3an1 (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_wb (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_clefin)) (syn_wo (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))) p0070 p0076
  have p0078 :=
    @g_sylibd (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_clefin)) (syn_wo (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) p0075 p0077
  have p0079 :=
    @g_n_3mix1 (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
  have p0080 :=
    @g_n_3mix2 (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
  have p0081 :=
    @g_jaoi (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0079 p0080
  have p0082 :=
    @g_syl6 (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (syn_wo (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) p0078 p0081
  have p0083 :=
    @g_ltfinp1 (.cv m) (syn_cnnc)
  have p0084 :=
    @g_sylan2 (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (.classMem (.cv m) (syn_cnnc)) (syn_wne (.cv m) (syn_c0)) (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) p0059 p0083
  have p0085 :=
    @g_n_3adant2 (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) (.classMem (.cv n) (syn_cnnc)) p0084
  have p0086 :=
    @g_opkeq1 (.cv m) (.cv n) (syn_cplc (.cv m) (syn_c1c))
  have p0087_e00_recanon : Nominal.NPrf (.imp (.objEq m n) (.classEq (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0086
  have p0087 :=
    @g_eleq1d (.objEq m n) (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin) p0087_e00_recanon
  have p0088 :=
    @g_syl5ibcom (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) p0085 p0087
  have p0089 :=
    @g_n_3mix3 (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
  have p0090 :=
    @g_syl6 (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.objEq m n) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) p0088 p0089
  have p0091 :=
    @g_ltfintr (.cv n) (.cv m) (syn_cplc (.cv m) (syn_c1c))
  have p0092 :=
    @g_syl3anc (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (.imp (syn_wa (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) p0072 p0069 p0071 p0091
  have p0093 :=
    @g_mpan2d (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) p0085 p0092
  have p0094 :=
    @g_syl6 (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) p0093 p0089
  have p0095 :=
    @g_n_3jaod (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) p0082 p0090 p0094
  have p0096 :=
    @g_embantd (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) p0060 p0095
  have p0097 :=
    @g_n_3expia (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (.imp (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))) p0096
  have p0098 :=
    @g_com23 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))) p0097
  have p0099 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.imp (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))))) p0098
  have p0100 :=
    @g_a2d (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))) p0099
  have p0101 :=
    @g_finds (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv k) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))))) (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (syn_c0c) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))))) (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))) (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))))) (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin))))) k m M (by exact (show k ∉ (M).fv from (by exact fresh_k_not_M))) (by exact (show k ∉ ((Wff.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((Wff.classMem (.cv n) (syn_cnnc))).fv) ∪ (((Wff.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))) (show k ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((syn_wne (.cv m) (syn_c0))).fv) ∪ (((syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_wne (.cv m) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show k ∉ (((Class.cv m)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))) (show k ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o]; exact (show k ∉ (((Wff.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))).fv) ∪ (((Wff.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin))).fv) ∪ (((Wff.objEq m n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((syn_copk (.cv n) (.cv m))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_copk (.cv n) (.cv m))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show k ∉ (((Class.cv n)).fv) ∪ (((Class.cv m)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))) (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))))))) (show k ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((syn_copk (.cv m) (.cv n))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_copk (.cv m) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show k ∉ (((Class.cv m)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))) (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))))))) (show k ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show k ∉ ((Wff.objEq m n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show k ∉ ({m, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show k ≠ m from (by exact fresh_k_ne_m)), (show k ≠ n from (by exact fresh_k_ne_n))⟩))))))))))))))))) (by exact (show m ∉ ((Wff.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv k) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((Wff.classMem (.cv n) (syn_cnnc))).fv) ∪ (((Wff.imp (syn_wne (.cv k) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n)))))) (show m ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((Wff.imp (syn_wne (.cv k) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wne (.cv k) (syn_c0))).fv) ∪ (((syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wne (.cv k) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show m ∉ (((Class.cv k)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))) (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o]; exact (show m ∉ (((Wff.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))).fv) ∪ (((Wff.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin))).fv) ∪ (((Wff.objEq k n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((syn_copk (.cv n) (.cv k))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_copk (.cv n) (.cv k))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show m ∉ (((Class.cv n)).fv) ∪ (((Class.cv k)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n)))))) (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))))))) (show m ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((Wff.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((syn_copk (.cv k) (.cv n))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_copk (.cv k) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show m ∉ (((Class.cv k)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))) (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n)))))))))) (show m ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show m ∉ ((Wff.objEq k n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show m ∉ ({k, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show m ≠ k from (by exact fresh_m_ne_k)), (show m ≠ n from (by exact fresh_m_ne_n))⟩))))))))))))))))) (by exact (show k ∉ ((Wff.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (syn_c0c) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((Wff.classMem (.cv n) (syn_cnnc))).fv) ∪ (((Wff.imp (syn_wne (syn_c0c) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))) (show k ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.imp (syn_wne (syn_c0c) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((syn_wne (syn_c0c) (syn_c0))).fv) ∪ (((syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_wne (syn_c0c) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show k ∉ (((syn_c0c)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show k ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o]; exact (show k ∉ (((Wff.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))).fv) ∪ (((Wff.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))).fv) ∪ (((Wff.classEq (syn_c0c) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((syn_copk (.cv n) (syn_c0c))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_copk (.cv n) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show k ∉ (((Class.cv n)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))) (show k ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((syn_copk (syn_c0c) (.cv n))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_copk (syn_c0c) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show k ∉ (((syn_c0c)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))))))) (show k ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show k ∉ ((Wff.classEq (syn_c0c) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show k ∉ (((syn_c0c)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n))))))))))))))))))))))) (by exact (show k ∉ ((Wff.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((Wff.classMem (.cv n) (syn_cnnc))).fv) ∪ (((Wff.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))) (show k ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((syn_wne M (syn_c0))).fv) ∪ (((syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_wne M (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show k ∉ ((M).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ (M).fv from (by exact fresh_k_not_M)) (show k ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o]; exact (show k ∉ (((Wff.classMem (syn_copk (.cv n) M) (syn_cltfin))).fv) ∪ (((Wff.classMem (syn_copk M (.cv n)) (syn_cltfin))).fv) ∪ (((Wff.classEq M (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.classMem (syn_copk (.cv n) M) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((syn_copk (.cv n) M)).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_copk (.cv n) M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show k ∉ (((Class.cv n)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))) (show k ∉ (M).fv from (by exact fresh_k_not_M)))))) (show k ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.classMem (syn_copk M (.cv n)) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((syn_copk M (.cv n))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_copk M (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show k ∉ ((M).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ (M).fv from (by exact fresh_k_not_M)) (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))))))) (show k ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show k ∉ ((Wff.classEq M (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show k ∉ ((M).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ (M).fv from (by exact fresh_k_not_M)) (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n))))))))))))))))))))))) (by exact (show k ∉ ((Wff.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((Wff.classMem (.cv n) (syn_cnnc))).fv) ∪ (((Wff.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))) (show k ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv) ∪ (((syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show k ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show k ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))) (show k ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o]; exact (show k ∉ (((Wff.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))).fv) ∪ (((Wff.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))).fv) ∪ (((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c)))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show k ∉ (((Class.cv n)).fv) ∪ (((syn_cplc (.cv m) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))) (show k ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show k ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))) (show k ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show k ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show k ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show k ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))) (show k ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n)))))))))) (show k ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show k ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show k ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show k ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))) (show k ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ n from (by exact fresh_k_ne_n))))))))))))))))))))))) (show k ≠ m from (by exact fresh_k_ne_m)) p0008 p0017 p0026 p0035 p0044 p0057 p0100
  have p0102 :=
    @g_com12 (.classMem M (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin)))) p0101
  have p0103 :=
    @g_vtoclga (.imp (.classMem M (syn_cnnc)) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n)) (.classMem (syn_copk (.cv n) M) (syn_cltfin))))) (.imp (.classMem M (syn_cnnc)) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin))))) n N (syn_cnnc) (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N))) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((Wff.imp (.classMem M (syn_cnnc)) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show n ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (M).fv from (by exact fresh_n_not_M)) (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show n ∉ ((Wff.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show n ∉ (((syn_wne M (syn_c0))).fv) ∪ (((syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_wne M (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show n ∉ ((M).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (M).fv from (by exact fresh_n_not_M)) (show n ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show n ∉ ((syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o]; exact (show n ∉ (((Wff.classMem (syn_copk N M) (syn_cltfin))).fv) ∪ (((Wff.classMem (syn_copk M N) (syn_cltfin))).fv) ∪ (((Wff.classEq M N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Wff.classMem (syn_copk N M) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((syn_copk N M)).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_copk N M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show n ∉ ((N).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (N).fv from (by exact fresh_n_not_N)) (show n ∉ (M).fv from (by exact fresh_n_not_M)))))) (show n ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show n ∉ ((Wff.classMem (syn_copk M N) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((syn_copk M N)).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_copk M N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show n ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (M).fv from (by exact fresh_n_not_M)) (show n ∉ (N).fv from (by exact fresh_n_not_N)))))) (show n ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show n ∉ ((Wff.classEq M N)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (M).fv from (by exact fresh_n_not_M)) (show n ∉ (N).fv from (by exact fresh_n_not_N))))))))))))))))))) p0007 p0102
  have p0104 :=
    @g_com12 (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc)) (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin)))) p0103
  have p0105 :=
    @g_n_3imp (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N) (.classMem (syn_copk N M) (syn_cltfin))) p0104
  exact p0105



#print axioms g_ltfintri

end NFChoice.DirectNominalPrf.WPPReplay
