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
import NominalWPPReplayChunk009StructuralPart042


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

noncomputable def g_ltfintrilem1
    (m : Var) (n : Var) (dv_m_n : m ≠ n) :
    Nominal.NPrf (.classMem (.cab m (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))) (syn_cvv)) := by
  let proofSupport : Finset Var := ({m} : Finset Var) ∪ ({n} : Finset Var)
  let t : Var := freshVar proofSupport 0
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_m : t ≠ m := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_m_ne_t : m ≠ t :=
    Ne.symm fresh_t_ne_m
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_t : n ≠ t :=
    Ne.symm fresh_t_ne_n
  have p0000 :=
    @g_unab (.neg (.classMem (.cv n) (syn_cnnc))) (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) m
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn m (syn_c0) (by exact (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0002 :=
    @g_elun (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))
  have p0003 :=
    @g_vex m
  have p0004 :=
    @g_elimak t (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)) (.cv m) (by exact (show t ∉ ((syn_ccnvk (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show t ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))) (by exact (show t ∉ ((syn_csn (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ n from (by exact fresh_t_ne_n))))))))) (by exact (show t ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ m from (by exact fresh_t_ne_m))))))) p0003
  have p0005 :=
    @g_vex n
  have p0006 :=
    @g_opkeq1 (.cv t) (.cv n) (.cv m)
  have p0007_e00_recanon : Nominal.NPrf (.imp (.objEq t n) (.classEq (syn_copk (.cv t) (.cv m)) (syn_copk (.cv n) (.cv m)))) :=
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
      p0006
  have p0007 :=
    @g_eleq1d (.objEq t n) (syn_copk (.cv t) (.cv m)) (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin)) p0007_e00_recanon
  have p0008_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv t) (.cv n)) (syn_wb (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cltfin))) (.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_ccnvk syn_wex syn_cltfin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0008 :=
    @g_rexsn (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cltfin))) (.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin))) t (.cv n) (by exact (show t ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ n from (by exact fresh_t_ne_n))))))) (by exact (show t ∉ ((Wff.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (.cv n) (.cv m))).fv) ∪ (((syn_ccnvk (syn_cltfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (.cv n) (.cv m))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv n)).fv) ∪ (((Class.cv m)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ n from (by exact fresh_t_ne_n)))))) (show t ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ m from (by exact fresh_t_ne_m)))))))))) (show t ∉ ((syn_ccnvk (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show t ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) p0005 p0008_e01_recanon
  have p0009 :=
    @g_bitri (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))) (syn_wrex t (syn_csn (.cv n)) (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cltfin)))) (.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin))) p0004 p0008
  have p0010 :=
    @g_opkelcnvk (.cv n) (.cv m) (syn_cltfin) p0005 p0003
  have p0011 :=
    @g_bitri (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))) (.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin))) (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) p0009 p0010
  have p0012 :=
    @g_elsnc (.cv m) (.cv n) p0003
  have p0013_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv m) (syn_csn (.cv n))) (.objEq m n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0012
  have p0013 :=
    @g_orbi12i (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))) (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.classMem (.cv m) (syn_csn (.cv n))) (.objEq m n) p0011 p0013_e01_recanon
  have p0014 :=
    @g_bitri (.classMem (.cv m) (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))) (syn_wo (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))) (.classMem (.cv m) (syn_csn (.cv n)))) (syn_wo (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)) p0002 p0013
  have p0015 :=
    @g_elimak t (syn_cltfin) (syn_csn (.cv n)) (.cv m) (by exact (show t ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show t ∉ ((syn_csn (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ n from (by exact fresh_t_ne_n))))))))) (by exact (show t ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ m from (by exact fresh_t_ne_m))))))) p0003
  have p0016_e00_recanon : Nominal.NPrf (.imp (.objEq t n) (.classEq (syn_copk (.cv t) (.cv m)) (syn_copk (.cv n) (.cv m)))) :=
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
      p0006
  have p0016 :=
    @g_eleq1d (.objEq t n) (syn_copk (.cv t) (.cv m)) (syn_copk (.cv n) (.cv m)) (syn_cltfin) p0016_e00_recanon
  have p0017_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv t) (.cv n)) (syn_wb (.classMem (syn_copk (.cv t) (.cv m)) (syn_cltfin)) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_cltfin syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0017 :=
    @g_rexsn (.classMem (syn_copk (.cv t) (.cv m)) (syn_cltfin)) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) t (.cv n) (by exact (show t ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ n from (by exact fresh_t_ne_n))))))) (by exact (show t ∉ ((Wff.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (.cv n) (.cv m))).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (.cv n) (.cv m))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv n)).fv) ∪ (((Class.cv m)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ n from (by exact fresh_t_ne_n)))))) (show t ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ m from (by exact fresh_t_ne_m)))))))))) (show t ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0005 p0017_e01_recanon
  have p0018 :=
    @g_bitri (.classMem (.cv m) (syn_cimak (syn_cltfin) (syn_csn (.cv n)))) (syn_wrex t (syn_csn (.cv n)) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cltfin))) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) p0015 p0017
  have p0019 :=
    @g_orbi12i (.classMem (.cv m) (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))) (syn_wo (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)) (.classMem (.cv m) (syn_cimak (syn_cltfin) (syn_csn (.cv n)))) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) p0014 p0018
  have p0020 :=
    @g_elun (.cv m) (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n)))
  have p0021 :=
    (by simpa [syn_wb, syn_w3o] using (Nominal.biimpRefl (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
  have p0022 :=
    @g_n_3bitr4i (syn_wo (.classMem (.cv m) (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))) (.classMem (.cv m) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))) (syn_wo (syn_wo (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))) (.classMem (.cv m) (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))) p0019 p0020 p0021
  have p0023 :=
    @g_eqabi (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))) m (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n)))) (by exact (show m ∉ ((syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show m ∉ (((syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))).fv) ∪ (((syn_cimak (syn_cltfin) (syn_csn (.cv n)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show m ∉ (((syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))).fv) ∪ (((syn_csn (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show m ∉ (((syn_ccnvk (syn_cltfin))).fv) ∪ (((syn_csn (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_ccnvk (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show m ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show m ∉ ((syn_csn (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact dv_m_n)))))))))))) (show m ∉ ((syn_csn (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact dv_m_n)))))))))))) (show m ∉ ((syn_cimak (syn_cltfin) (syn_csn (.cv n)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show m ∉ (((syn_cltfin)).fv) ∪ (((syn_csn (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show m ∉ ((syn_csn (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact dv_m_n))))))))))))))))) p0022
  have p0024 :=
    @g_uneq12i (syn_csn (syn_c0)) (.cab m (.classEq (.cv m) (syn_c0))) (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n)))) (.cab m (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) p0001 p0023
  have p0025 :=
    @g_unab (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))) m
  have p0026 :=
    @g_eqtri (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))) (syn_cun (.cab m (.classEq (.cv m) (syn_c0))) (.cab m (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))) (.cab m (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))) p0024 p0025
  have p0027 :=
    @g_uneq2i (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))) (.cab m (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))) (.cab m (.neg (.classMem (.cv n) (syn_cnnc)))) p0026
  have p0028 :=
    @g_imor (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
  have p0029 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv m) (syn_c0))))
  have p0030 :=
    @g_imbi1i (syn_wne (.cv m) (syn_c0)) (.neg (.classEq (.cv m) (syn_c0))) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))) p0029
  have p0031 :=
    (by simpa [syn_wb, syn_wo] using (Nominal.biimpRefl (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))))
  have p0032 :=
    @g_bitr4i (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) (.imp (.neg (.classEq (.cv m) (syn_c0))) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) p0030 p0031
  have p0033 :=
    @g_orbi2i (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) (.neg (.classMem (.cv n) (syn_cnnc))) p0032
  have p0034 :=
    @g_bitri (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))) (syn_wo (.neg (.classMem (.cv n) (syn_cnnc))) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))) (syn_wo (.neg (.classMem (.cv n) (syn_cnnc))) (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))) p0028 p0033
  have p0035 :=
    @g_abbii (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))) (syn_wo (.neg (.classMem (.cv n) (syn_cnnc))) (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))) m p0034
  have p0036 :=
    @g_n_3eqtr4i (syn_cun (.cab m (.neg (.classMem (.cv n) (syn_cnnc)))) (.cab m (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))) (.cab m (syn_wo (.neg (.classMem (.cv n) (syn_cnnc))) (syn_wo (.classEq (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))) (syn_cun (.cab m (.neg (.classMem (.cv n) (syn_cnnc)))) (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n)))))) (.cab m (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))) p0000 p0027 p0035
  have p0037 :=
    @g_abexv (.neg (.classMem (.cv n) (syn_cnnc))) m (by exact (show m ∉ ((Wff.neg (.classMem (.cv n) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show m ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact dv_m_n)))))) (show m ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))
  have p0038 :=
    @g_snex (syn_c0)
  have p0039 :=
    @g_ltfinex
  have p0040 :=
    @g_cnvkex (syn_cltfin) p0039
  have p0041 :=
    @g_snex (.cv n)
  have p0042 :=
    @g_imakex (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)) p0040 p0041
  have p0043 :=
    @g_unex (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)) p0042 p0041
  have p0044 :=
    @g_ltfinex
  have p0045 :=
    @g_imakex (syn_cltfin) (syn_csn (.cv n)) p0044 p0041
  have p0046 :=
    @g_unex (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n))) p0043 p0045
  have p0047 :=
    @g_unex (syn_csn (syn_c0)) (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n)))) p0038 p0046
  have p0048 :=
    @g_unex (.cab m (.neg (.classMem (.cv n) (syn_cnnc)))) (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))) p0037 p0047
  have p0049 :=
    @g_eqeltrri (syn_cun (.cab m (.neg (.classMem (.cv n) (syn_cnnc)))) (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n)))))) (.cab m (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0)) (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))) (syn_cvv) p0036 p0048
  exact p0049



#print axioms g_ltfintrilem1

end NFChoice.DirectNominalPrf.WPPReplay
