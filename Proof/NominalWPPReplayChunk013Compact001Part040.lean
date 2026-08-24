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
import NominalWPPReplayChunk013Compact001Part039

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

noncomputable def g_enprmaplem4
    (x : Var) (y : Var) (u : Var) (B : Class) (R : Class) (p : Var) (dv_B_u : u ∉ B.fv) (dv_p_u : p ≠ u) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (hyp_enprmaplem4_1 : Nominal.NPrf (.classEq R (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y))))) (hyp_enprmaplem4_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem R (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({u} : Finset Var) ∪ B.fv ∪ R.fv ∪ ({p} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_p : z ≠ p := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have dv_cache_0001 : u ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_p_u), dv_u_x, dv_u_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_cif (.objMem u p) (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_u, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have p0000 :=
    @g_elun (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))
  have p0001 :=
    @g_opelxp (.cv u) (syn_csn (.cv z)) (.cv p) (syn_cpw1 (.cv x))
  have p0002 :=
    @g_snelpw1 (.cv z) (.cv x)
  have p0003_e00_recanon : Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0002
  have p0003 :=
    @g_anbi2i (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))) (.objMem z x) (.objMem u p) p0003_e00_recanon
  have p0004_e00_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (.cv p) (syn_cpw1 (.cv x)))) (syn_wa (.objMem u p) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_cxp syn_copab syn_cpw1 syn_cin syn_cpw syn_wss syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0001
  have p0004 :=
    @g_bitri (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (.cv p) (syn_cpw1 (.cv x)))) (syn_wa (.objMem u p) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x)))) (syn_wa (.objMem u p) (.objMem z x)) p0004_e00_recanon p0003
  have p0005 :=
    @g_opelxp (.cv u) (syn_csn (.cv z)) (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))
  have p0006 :=
    @g_vex u
  have p0007 :=
    @g_elcompl (.cv u) (.cv p) p0006
  have p0008 :=
    @g_snelpw1 (.cv z) (.cv y)
  have p0009_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv u) (syn_ccompl (.cv p))) (.neg (.objMem u p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0009_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0008
  have p0009 :=
    @g_anbi12i (.classMem (.cv u) (syn_ccompl (.cv p))) (.neg (.objMem u p)) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y) p0009_e00_recanon p0009_e01_recanon
  have p0010 :=
    @g_bitri (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))) (syn_wa (.classMem (.cv u) (syn_ccompl (.cv p))) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y)))) (syn_wa (.neg (.objMem u p)) (.objMem z y)) p0005 p0009
  have p0011 :=
    @g_orbi12i (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (.cv p) (syn_cpw1 (.cv x)))) (syn_wa (.objMem u p) (.objMem z x)) (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))) (syn_wa (.neg (.objMem u p)) (.objMem z y)) p0004 p0010
  have p0012 :=
    @g_bitri (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))) (syn_wo (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (.cv p) (syn_cpw1 (.cv x)))) (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))) (syn_wo (syn_wa (.objMem u p) (.objMem z x)) (syn_wa (.neg (.objMem u p)) (.objMem z y))) p0000 p0011
  have p0013 :=
    @g_opelcnv (syn_csn (.cv z)) (.cv u) (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))
  have p0014 :=
    @g_elif (.objMem u p) (.cv z) (.cv x) (.cv y)
  have p0015_e02_recanon : Nominal.NPrf (syn_wb (.classMem (.cv z) (syn_cif (.objMem u p) (.cv x) (.cv y))) (syn_wo (syn_wa (.objMem u p) (.objMem z x)) (syn_wa (.neg (.objMem u p)) (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cif syn_wo syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_neg]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0014
  have p0015 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))) (syn_wo (syn_wa (.objMem u p) (.objMem z x)) (syn_wa (.neg (.objMem u p)) (.objMem z y))) (.classMem (syn_cop (syn_csn (.cv z)) (.cv u)) (syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))))) (.classMem (.cv z) (syn_cif (.objMem u p) (.cv x) (.cv y))) p0012 p0013 p0015_e02_recanon
  have p0016 :=
    @g_releqmpt u z B (syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))) (syn_cif (.objMem u p) (.cv x) (.cv y)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0015
  have p0017 :=
    @g_eqtr4i R (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y))) (syn_cin (syn_cxp B (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))))) (syn_c1c))))) hyp_enprmaplem4_1 p0016
  have p0018 :=
    @g_vex p
  have p0019 :=
    @g_vex x
  have p0020 :=
    @g_pw1ex (.cv x) p0019
  have p0021 :=
    @g_xpex (.cv p) (syn_cpw1 (.cv x)) p0018 p0020
  have p0022 :=
    @g_complex (.cv p) p0018
  have p0023 :=
    @g_vex y
  have p0024 :=
    @g_pw1ex (.cv y) p0023
  have p0025 :=
    @g_xpex (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)) p0022 p0024
  have p0026 :=
    @g_unex (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))) p0021 p0025
  have p0027 :=
    @g_cnvex (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y)))) p0026
  have p0028 :=
    @g_mptexlem B (syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))) hyp_enprmaplem4_2 p0027
  have p0029 :=
    @g_eqeltri R (syn_cin (syn_cxp B (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_ccnv (syn_cun (syn_cxp (.cv p) (syn_cpw1 (.cv x))) (syn_cxp (syn_ccompl (.cv p)) (syn_cpw1 (.cv y))))))) (syn_c1c))))) (syn_cvv) p0017 p0028
  exact p0029

noncomputable def g_enprmaplem5
    (x : Var) (y : Var) (u : Var) (A : Class) (B : Class) (R : Class) (W : Class) (r : Var) (p : Var) (dv_A_p : p ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_B_r : r ∉ B.fv) (dv_B_u : u ∉ B.fv) (dv_R_r : r ∉ R.fv) (dv_W_p : p ∉ W.fv) (dv_p_u : p ≠ u) (dv_p_x : p ≠ x) (dv_p_y : p ≠ y) (dv_r_x : r ≠ x) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (hyp_enprmaplem5_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))))) (hyp_enprmaplem5_2 : Nominal.NPrf (.classEq R (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y))))) (hyp_enprmaplem5_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wss (syn_cpw B) (syn_crn W))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ W.fv ∪ ({r} : Finset Var) ∪ ({p} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_r_ne_z : r ≠ z :=
    Ne.symm fresh_z_ne_r
  have fresh_z_ne_p : z ≠ p := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have dv_cache_0001 : u ∉ ((Wff.classEq A (syn_cpr (.cv x) (.cv y)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, dv_u_x, dv_u_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show p ≠ u from (by exact dv_p_u))
  have dv_cache_0005 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0006 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ y from (by exact dv_u_y))
  have dv_cache_0007 : r ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((syn_cima (syn_ccnv R) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_r, dv_r_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : r ∉ ((syn_co A (syn_cmap) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, dv_B_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((syn_cif (.objMem z p) (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_u_x, dv_u_y, fresh_u_ne_z, (Ne.symm dv_p_u), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_cima (syn_ccnv R) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, fresh_z_not_B, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : r ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : r ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((syn_cpw B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_crn W)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_W_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_p_x, dv_p_y, dv_A_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex p
  have p0001 :=
    @g_elpw (.cv p) B p0000
  have p0002 :=
    @g_ifeqor (.objMem u p) (.cv x) (.cv y)
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_vex y
  have p0005 :=
    @g_ifex (.objMem u p) (.cv x) (.cv y) p0003 p0004
  have p0006 :=
    @g_elpr (syn_cif (.objMem u p) (.cv x) (.cv y)) (.cv x) (.cv y) p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cpr (.cv x) (.cv y))) (syn_wo (.classEq (syn_cif (.objMem u p) (.cv x) (.cv y)) (.cv x)) (.classEq (syn_cif (.objMem u p) (.cv x) (.cv y)) (.cv y))) p0002 p0006
  have p0008 :=
    @g_id (.classEq A (syn_cpr (.cv x) (.cv y)))
  have p0009 :=
    @g_syl5eleqr (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cpr (.cv x) (.cv y)) A p0007 p0008
  have p0010 :=
    @g_ralrimivw (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) A) u B dv_cache_0001 p0009
  have p0011 :=
    @g_fmpt u B A (syn_cif (.objMem u p) (.cv x) (.cv y)) R dv_cache_0002 dv_cache_0003 hyp_enprmaplem5_2
  have p0012 :=
    @g_sylib (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wral u B (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) A)) (syn_wf R B A) p0010 p0011
  have p0013 :=
    @g_prex (.cv x) (.cv y)
  have p0014 :=
    @g_eleq1 A (syn_cpr (.cv x) (.cv y)) (syn_cvv)
  have p0015 :=
    @g_mpbiri (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem A (syn_cvv)) (.classMem (syn_cpr (.cv x) (.cv y)) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_enprmaplem4 x y u B R p dv_cache_0002 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_enprmaplem5_2 hyp_enprmaplem5_3
  have p0017 :=
    @g_elmapg A B R (syn_cvv) (syn_cvv) (syn_cvv)
  have p0018 :=
    @g_mp3an23 (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem R (syn_cvv)) (syn_wb (.classMem R (syn_co A (syn_cmap) B)) (syn_wf R B A)) hyp_enprmaplem5_3 p0016 p0017
  have p0019 :=
    @g_syl (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem A (syn_cvv)) (syn_wb (.classMem R (syn_co A (syn_cmap) B)) (syn_wf R B A)) p0015 p0018
  have p0020 :=
    @g_mpbird (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem R (syn_co A (syn_cmap) B)) (syn_wf R B A) p0012 p0019
  have p0021 :=
    @g_n_3ad2ant2 (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wne (.cv x) (.cv y)) (.classMem R (syn_co A (syn_cmap) B)) (syn_wss (.cv p) B) p0020
  have p0022 :=
    @g_cnveq (.cv r) R
  have p0023 :=
    @g_imaeq1d (.classEq (.cv r) R) (syn_ccnv (.cv r)) (syn_ccnv R) (syn_csn (.cv x)) p0022
  have p0024 :=
    @g_cnvex R p0016
  have p0025 :=
    @g_snex (.cv x)
  have p0026 :=
    @g_imaex (syn_ccnv R) (syn_csn (.cv x)) p0024 p0025
  have p0027 :=
    @g_fvmpt r R (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cima (syn_ccnv R) (syn_csn (.cv x))) (syn_co A (syn_cmap) B) W dv_cache_0007 dv_cache_0008 dv_cache_0009 p0023 hyp_enprmaplem5_1 p0026
  have p0028 :=
    @g_syl (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.classMem R (syn_co A (syn_cmap) B)) (.classEq (syn_cfv W R) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0021 p0027
  have p0029 :=
    @g_eliniseg R (.cv x) (.cv z)
  have p0030 :=
    @g_breldm (.cv z) (.cv x) R
  have p0031 :=
    @g_fnmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y)) R (syn_cvv) dv_cache_0002 hyp_enprmaplem5_2
  have p0032 :=
    @g_a1i (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cvv)) (.classMem (.cv u) B) p0005
  have p0033 :=
    @g_mprg (.classMem (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cvv)) (syn_wfn R B) u B p0031 p0032
  have p0034 :=
    @g_fndm B R
  have p0035 :=
    Nominal.mp p0033 p0034
  have p0036 :=
    @g_syl6eleq (syn_wbr (.cv z) R (.cv x)) (.cv z) (syn_cdm R) B p0030 p0035
  have p0037 :=
    @g_fnbrfvb B (.cv z) (.cv x) R
  have p0038 :=
    @g_mpan (syn_wfn R B) (.classMem (.cv z) B) (syn_wb (.classEq (syn_cfv R (.cv z)) (.cv x)) (syn_wbr (.cv z) R (.cv x))) p0033 p0037
  have p0039 :=
    @g_biimprd (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x)) (syn_wbr (.cv z) R (.cv x)) p0038
  have p0040 :=
    @g_com12 (.classMem (.cv z) B) (syn_wbr (.cv z) R (.cv x)) (.classEq (syn_cfv R (.cv z)) (.cv x)) p0039
  have p0041 :=
    @g_jcai (syn_wbr (.cv z) R (.cv x)) (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x)) p0036 p0040
  have p0042 :=
    @g_eleq1 (.cv u) (.cv z) (.cv p)
  have p0043_e00_recanon : Nominal.NPrf (.imp (.objEq u z) (syn_wb (.objMem u p) (.objMem z p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0042
  have p0043 :=
    @g_ifbid (.objEq u z) (.objMem u p) (.objMem z p) (.cv x) (.cv y) p0043_e00_recanon
  have p0044 :=
    @g_ifex (.objMem z p) (.cv x) (.cv y) p0003 p0004
  have p0045_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv u) (.cv z)) (.classEq (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cif (.objMem z p) (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cif syn_wo syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0043
  have p0045 :=
    @g_fvmpt u (.cv z) (syn_cif (.objMem u p) (.cv x) (.cv y)) (syn_cif (.objMem z p) (.cv x) (.cv y)) B R dv_cache_0010 dv_cache_0011 dv_cache_0002 p0045_e00_recanon hyp_enprmaplem5_2 p0044
  have p0046 :=
    @g_eqeq1d (.classMem (.cv z) B) (syn_cfv R (.cv z)) (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x) p0045
  have p0047 :=
    @g_biimpd (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x)) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)) p0046
  have p0048 :=
    @g_imp (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x)) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)) p0047
  have p0049 :=
    @g_simpl1 (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x))
  have p0050 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv x) (.cv y))))
  have p0051_e01_recanon : Nominal.NPrf (syn_wb (syn_wne (.cv x) (.cv y)) (.neg (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0050
  have p0051 :=
    @g_sylib (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x))) (syn_wne (.cv x) (.cv y)) (.neg (.objEq x y)) p0049 p0051_e01_recanon
  have p0052 :=
    @g_iffalse (.objMem z p) (.cv x) (.cv y)
  have p0053 :=
    @g_eqeq2d (.neg (.objMem z p)) (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv y) (.cv x) p0052
  have p0054_e00_recanon : Nominal.NPrf (.imp (.neg (.objMem z p)) (syn_wb (.classEq (.cv x) (syn_cif (.objMem z p) (.cv x) (.cv y))) (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cif syn_wo syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
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
      p0053
  have p0054 :=
    @g_biimpd (.neg (.objMem z p)) (.classEq (.cv x) (syn_cif (.objMem z p) (.cv x) (.cv y))) (.objEq x y) p0054_e00_recanon
  have p0055 :=
    @g_com12 (.neg (.objMem z p)) (.classEq (.cv x) (syn_cif (.objMem z p) (.cv x) (.cv y))) (.objEq x y) p0054
  have p0056 :=
    @g_eqcoms (.imp (.neg (.objMem z p)) (.objEq x y)) (.cv x) (syn_cif (.objMem z p) (.cv x) (.cv y)) p0055
  have p0057 :=
    @g_adantl (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)) (.imp (.neg (.objMem z p)) (.objEq x y)) (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) p0056
  have p0058 :=
    @g_mt3d (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x))) (.objMem z p) (.objEq x y) p0051 p0057
  have p0059 :=
    @g_ex (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)) (.objMem z p) p0058
  have p0060 :=
    @g_syl5 (syn_wa (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x))) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)) (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.objMem z p) p0048 p0059
  have p0061 :=
    @g_syl5 (syn_wbr (.cv z) R (.cv x)) (syn_wa (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (.cv x))) (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.objMem z p) p0041 p0060
  have p0062 :=
    @g_ssel2 (.cv p) B (.cv z)
  have p0063_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wss (.cv p) B) (.objMem z p)) (.classMem (.cv z) B)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0062
  have p0063 :=
    @g_n_3ad2antl3 (syn_wss (.cv p) B) (syn_wne (.cv x) (.cv y)) (.objMem z p) (.classMem (.cv z) B) (.classEq A (syn_cpr (.cv x) (.cv y))) p0063_e00_recanon
  have p0064 :=
    @g_syl (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.objMem z p)) (.classMem (.cv z) B) (.classEq (syn_cfv R (.cv z)) (syn_cif (.objMem z p) (.cv x) (.cv y))) p0063 p0045
  have p0065 :=
    @g_iftrue (.objMem z p) (.cv x) (.cv y)
  have p0066 :=
    @g_adantl (.objMem z p) (.classEq (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x)) (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) p0065
  have p0067 :=
    @g_eqtrd (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.objMem z p)) (syn_cfv R (.cv z)) (syn_cif (.objMem z p) (.cv x) (.cv y)) (.cv x) p0064 p0066
  have p0068 :=
    @g_syl (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.objMem z p)) (.classMem (.cv z) B) (syn_wb (.classEq (syn_cfv R (.cv z)) (.cv x)) (syn_wbr (.cv z) R (.cv x))) p0063 p0038
  have p0069 :=
    @g_mpbid (syn_wa (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.objMem z p)) (.classEq (syn_cfv R (.cv z)) (.cv x)) (syn_wbr (.cv z) R (.cv x)) p0067 p0068
  have p0070 :=
    @g_ex (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.objMem z p) (syn_wbr (.cv z) R (.cv x)) p0069
  have p0071 :=
    @g_impbid (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (syn_wbr (.cv z) R (.cv x)) (.objMem z p) p0061 p0070
  have p0072 :=
    @g_syl5bb (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_wbr (.cv z) R (.cv x)) (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.objMem z p) p0029 p0071
  have p0073_e00_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (syn_wb (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (.classMem (.cv z) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wne syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_wss syn_cin syn_wb syn_cima syn_wrex syn_wex syn_wbr syn_cop syn_ccnv syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0072
  have p0073 :=
    @g_eqrdv (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) z (syn_cima (syn_ccnv R) (syn_csn (.cv x))) (.cv p) dv_cache_0012 dv_cache_0013 dv_cache_0014 p0073_e00_recanon
  have p0074 :=
    @g_eqtrd (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (syn_cfv W R) (syn_cima (syn_ccnv R) (syn_csn (.cv x))) (.cv p) p0028 p0073
  have p0075 :=
    @g_enprmaplem2 x A B W r dv_cache_0015 dv_cache_0016 hyp_enprmaplem5_1
  have p0076 :=
    @g_fnbrfvb (syn_co A (syn_cmap) B) R (.cv p) W
  have p0077 :=
    @g_mpan (syn_wfn W (syn_co A (syn_cmap) B)) (.classMem R (syn_co A (syn_cmap) B)) (syn_wb (.classEq (syn_cfv W R) (.cv p)) (syn_wbr R W (.cv p))) p0075 p0076
  have p0078 :=
    @g_syl (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.classMem R (syn_co A (syn_cmap) B)) (syn_wb (.classEq (syn_cfv W R) (.cv p)) (syn_wbr R W (.cv p))) p0021 p0077
  have p0079 :=
    @g_mpbid (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B)) (.classEq (syn_cfv W R) (.cv p)) (syn_wbr R W (.cv p)) p0074 p0078
  have p0080 :=
    @g_n_3expia (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wss (.cv p) B) (syn_wbr R W (.cv p)) p0079
  have p0081 :=
    @g_brelrn R (.cv p) W
  have p0082 :=
    @g_syl6 (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wss (.cv p) B) (syn_wbr R W (.cv p)) (.classMem (.cv p) (syn_crn W)) p0080 p0081
  have p0083 :=
    @g_syl5bi (.classMem (.cv p) (syn_cpw B)) (syn_wss (.cv p) B) (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.classMem (.cv p) (syn_crn W)) p0001 p0082
  have p0084 :=
    @g_ssrdv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) p (syn_cpw B) (syn_crn W) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0083
  exact p0084

#print axioms g_enprmaplem5

end NFChoice.DirectNominalPrf.WPPReplay
