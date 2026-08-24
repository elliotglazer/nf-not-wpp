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
import NominalWPPReplayChunk009StructuralPart016


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

noncomputable def g_ins2kexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cins2k A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_V : t ∉ V.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_w_ne_y : w ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_t_ne_y : t ≠ y := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have p0000 :=
    @g_ins2keq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cins2k (.cv x)) (syn_cins2k A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axIns2 x y z w t (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w)) (show x ≠ t from (by exact fresh_x_ne_t)) (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w)) (show y ≠ t from (by exact fresh_y_ne_t)) (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ t from (by exact fresh_z_ne_t)) (show w ≠ t from (by exact fresh_w_ne_t))
  have p0003 :=
    @g_inss1 (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)
  have p0004 :=
    @g_ins2kss (.cv x)
  have p0005 :=
    @g_insklem z w t (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)) (syn_cins2k (.cv x)) (by exact (show z ∉ ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show z ∉ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))) (by exact (show w ∉ ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show w ∉ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show w ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))))) (by exact (show t ∉ ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show t ∉ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y))))))))))) (by exact (show z ∉ ((syn_cins2k (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))))) (by exact (show w ∉ ((syn_cins2k (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x))))))))) (by exact (show t ∉ ((syn_cins2k (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))) (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ t from (by exact fresh_z_ne_t)) (show w ≠ t from (by exact fresh_w_ne_t)) p0003 p0004
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_snel1c (.cv z) p0006
  have p0008 :=
    @g_snelpw1 (syn_csn (.cv z)) (syn_c1c)
  have p0009 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (.cv z))) (syn_cpw1 (syn_c1c))) (.classMem (syn_csn (.cv z)) (syn_c1c)) p0007 p0008
  have p0010 :=
    @g_vex w
  have p0011 :=
    @g_vex t
  have p0012 :=
    @g_opkelxpk (.cv w) (.cv t) (syn_cvv) (syn_cvv) p0010 p0011
  have p0013 :=
    @g_mpbir2an (.classMem (syn_copk (.cv w) (.cv t)) (syn_cxpk (syn_cvv) (syn_cvv))) (.classMem (.cv w) (syn_cvv)) (.classMem (.cv t) (syn_cvv)) p0010 p0011 p0012
  have p0014 :=
    @g_snex (syn_csn (.cv z))
  have p0015 :=
    @g_opkex (.cv w) (.cv t)
  have p0016 :=
    @g_opkelxpk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)) (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_mpbir2an (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.classMem (syn_csn (syn_csn (.cv z))) (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv w) (.cv t)) (syn_cxpk (syn_cvv) (syn_cvv))) p0009 p0013 p0016
  have p0018 :=
    @g_elin (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)
  have p0019 :=
    @g_mpbiran (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) p0017 p0018
  have p0020 :=
    @g_otkelins2k (.cv z) (.cv w) (.cv t) (.cv x) p0006 p0010 p0011
  have p0021 :=
    @g_bibi12i (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cins2k (.cv x))) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x)) p0019 p0020
  have p0022 :=
    @g_albii (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cins2k (.cv x)))) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x))) t p0021
  have p0023 :=
    @g_n_2albii (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cins2k (.cv x))))) (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x)))) z w p0022
  have p0024 :=
    @g_bitri (.classEq (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)) (syn_cins2k (.cv x))) (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cins2k (.cv x))))))) (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x)))))) p0005 p0023
  have p0025 :=
    @g_biimpri (.classEq (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)) (syn_cins2k (.cv x))) (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x)))))) p0024
  have p0026 :=
    @g_n_1cex
  have p0027 :=
    @g_pw1ex (syn_c1c) p0026
  have p0028 :=
    @g_vvex
  have p0029 :=
    @g_vvex
  have p0030 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0028 p0029
  have p0031 :=
    @g_xpkex (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0027 p0030
  have p0032 :=
    @g_vex y
  have p0033 :=
    @g_inex (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y) p0031 p0032
  have p0034 :=
    @g_syl6eqelr (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x)))))) (syn_cins2k (.cv x)) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)) (syn_cvv) p0025 p0033
  have p0035 :=
    @g_exlimiv (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x)))))) (.classMem (syn_cins2k (.cv x)) (syn_cvv)) y (by exact (show y ∉ ((Wff.classMem (syn_cins2k (.cv x)) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_cins2k (.cv x))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cins2k (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0034
  have p0036 :=
    Nominal.mp p0002 p0035
  have p0037 :=
    @g_vtoclg (.classMem (syn_cins2k (.cv x)) (syn_cvv)) (.classMem (syn_cins2k A) (syn_cvv)) x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((Wff.classMem (syn_cins2k A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_cins2k A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins2k A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0001 p0036
  exact p0037

noncomputable def g_ins3kexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cins3k A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_V : t ∉ V.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_w_ne_y : w ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_t_ne_y : t ≠ y := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have p0000 :=
    @g_ins3keq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cins3k (.cv x)) (syn_cins3k A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axIns3 x y z w t (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w)) (show x ≠ t from (by exact fresh_x_ne_t)) (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w)) (show y ≠ t from (by exact fresh_y_ne_t)) (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ t from (by exact fresh_z_ne_t)) (show w ≠ t from (by exact fresh_w_ne_t))
  have p0003 :=
    @g_inss1 (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)
  have p0004 :=
    @g_ins3kss (.cv x)
  have p0005 :=
    @g_insklem z w t (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)) (syn_cins3k (.cv x)) (by exact (show z ∉ ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show z ∉ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))) (by exact (show w ∉ ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show w ∉ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show w ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))))) (by exact (show t ∉ ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show t ∉ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y))))))))))) (by exact (show z ∉ ((syn_cins3k (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))))) (by exact (show w ∉ ((syn_cins3k (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x))))))))) (by exact (show t ∉ ((syn_cins3k (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))) (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ t from (by exact fresh_z_ne_t)) (show w ≠ t from (by exact fresh_w_ne_t)) p0003 p0004
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_snel1c (.cv z) p0006
  have p0008 :=
    @g_snelpw1 (syn_csn (.cv z)) (syn_c1c)
  have p0009 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (.cv z))) (syn_cpw1 (syn_c1c))) (.classMem (syn_csn (.cv z)) (syn_c1c)) p0007 p0008
  have p0010 :=
    @g_vex w
  have p0011 :=
    @g_vex t
  have p0012 :=
    @g_opkelxpk (.cv w) (.cv t) (syn_cvv) (syn_cvv) p0010 p0011
  have p0013 :=
    @g_mpbir2an (.classMem (syn_copk (.cv w) (.cv t)) (syn_cxpk (syn_cvv) (syn_cvv))) (.classMem (.cv w) (syn_cvv)) (.classMem (.cv t) (syn_cvv)) p0010 p0011 p0012
  have p0014 :=
    @g_snex (syn_csn (.cv z))
  have p0015 :=
    @g_opkex (.cv w) (.cv t)
  have p0016 :=
    @g_opkelxpk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)) (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_mpbir2an (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.classMem (syn_csn (syn_csn (.cv z))) (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv w) (.cv t)) (syn_cxpk (syn_cvv) (syn_cvv))) p0009 p0013 p0016
  have p0018 :=
    @g_elin (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)
  have p0019 :=
    @g_mpbiran (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) p0017 p0018
  have p0020 :=
    @g_otkelins3k (.cv z) (.cv w) (.cv t) (.cv x) p0006 p0010 p0011
  have p0021 :=
    @g_bibi12i (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cins3k (.cv x))) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)) p0019 p0020
  have p0022 :=
    @g_n_2albii (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cins3k (.cv x)))) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))) w t p0021
  have p0023 :=
    @g_albii (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cins3k (.cv x)))))) (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))) z p0022
  have p0024 :=
    @g_bitri (.classEq (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)) (syn_cins3k (.cv x))) (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))) (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (syn_cins3k (.cv x))))))) (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))) p0005 p0023
  have p0025 :=
    @g_biimpri (.classEq (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)) (syn_cins3k (.cv x))) (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))) p0024
  have p0026 :=
    @g_n_1cex
  have p0027 :=
    @g_pw1ex (syn_c1c) p0026
  have p0028 :=
    @g_vvex
  have p0029 :=
    @g_vvex
  have p0030 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0028 p0029
  have p0031 :=
    @g_xpkex (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0027 p0030
  have p0032 :=
    @g_vex y
  have p0033 :=
    @g_inex (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y) p0031 p0032
  have p0034 :=
    @g_syl6eqelr (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))) (syn_cins3k (.cv x)) (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)) (syn_cvv) p0025 p0033
  have p0035 :=
    @g_exlimiv (.all z (.all w (.all t (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))) (.classMem (syn_cins3k (.cv x)) (syn_cvv)) y (by exact (show y ∉ ((Wff.classMem (syn_cins3k (.cv x)) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_cins3k (.cv x))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cins3k (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0034
  have p0036 :=
    Nominal.mp p0002 p0035
  have p0037 :=
    @g_vtoclg (.classMem (syn_cins3k (.cv x)) (syn_cvv)) (.classMem (syn_cins3k A) (syn_cvv)) x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((Wff.classMem (syn_cins3k A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_cins3k A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins3k A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0001 p0036
  exact p0037

noncomputable def g_ins2kex
    (A : Class) (hyp_inskex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins2k A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ins2kexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_inskex_1 p0000
  exact p0001

noncomputable def g_ins3kex
    (A : Class) (hyp_inskex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins3k A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ins3kexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_inskex_1 p0000
  exact p0001

noncomputable def g_cokexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_ccomk A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    (by simpa [syn_ccomk] using (Nominal.classEqRefl (syn_ccomk A B)))
  have p0001 :=
    @g_ins2kexg A V
  have p0002 :=
    @g_cnvkexg B W
  have p0003 :=
    @g_ins3kexg (syn_ccnvk B) (syn_cvv)
  have p0004 :=
    @g_syl (.classMem B W) (.classMem (syn_ccnvk B) (syn_cvv)) (.classMem (syn_cins3k (syn_ccnvk B)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_inexg (syn_cins2k A) (syn_cins3k (syn_ccnvk B)) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_syl2an (.classMem A V) (.classMem (syn_cins2k A) (syn_cvv)) (.classMem (syn_cins3k (syn_ccnvk B)) (syn_cvv)) (.classMem (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv)) (.classMem B W) p0001 p0004 p0005
  have p0007 :=
    @g_vvex
  have p0008 :=
    @g_imakexg (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_sylancl (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv)) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cimak (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv)) (syn_cvv)) p0006 p0007 p0008
  have p0010 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_ccomk A B) (syn_cimak (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv)) (syn_cvv) p0000 p0009
  exact p0010

noncomputable def g_cokex
    (A : Class) (B : Class) (hyp_cokex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_cokex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ccomk A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_cokexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_ccomk A B) (syn_cvv)) hyp_cokex_1 hyp_cokex_2 p0000
  exact p0001

noncomputable def g_imagekexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cimagek A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_cimagek] using (Nominal.classEqRefl (syn_cimagek A)))
  have p0001 :=
    @g_sikexg A V
  have p0002 :=
    @g_cnvkexg (syn_csik A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A V) (.classMem (syn_csik A) (syn_cvv)) (.classMem (syn_ccnvk (syn_csik A)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_ssetkex
  have p0005 :=
    @g_cokexg (syn_cssetk) (syn_ccnvk (syn_csik A)) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_mpan (.classMem (syn_cssetk) (syn_cvv)) (.classMem (syn_ccnvk (syn_csik A)) (syn_cvv)) (.classMem (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_syl (.classMem A V) (.classMem (syn_ccnvk (syn_csik A)) (syn_cvv)) (.classMem (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_ins3kexg (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A V) (.classMem (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))) (syn_cvv)) (.classMem (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_ssetkex
  have p0011 :=
    @g_ins2kex (syn_cssetk) p0010
  have p0012 :=
    @g_symdifexg (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_mpan (.classMem (syn_cins2k (syn_cssetk)) (syn_cvv)) (.classMem (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))) (syn_cvv)) (.classMem (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_syl (.classMem A V) (.classMem (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))) (syn_cvv)) (.classMem (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cvv)) p0009 p0013
  have p0015 :=
    @g_n_1cex
  have p0016 :=
    @g_pw1ex (syn_c1c) p0015
  have p0017 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0016
  have p0018 :=
    @g_imakexg (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cvv) (syn_cvv)
  have p0019 :=
    @g_mpan2 (.classMem (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cvv)) (.classMem (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cvv)) (.classMem (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cvv)) p0017 p0018
  have p0020 :=
    @g_syl (.classMem A V) (.classMem (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cvv)) (.classMem (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cvv)) p0014 p0019
  have p0021 :=
    @g_vvex
  have p0022 :=
    @g_vvex
  have p0023 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0021 p0022
  have p0024 :=
    @g_difexg (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_mpan (.classMem (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (.classMem (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cvv)) (.classMem (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_syl (.classMem A V) (.classMem (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cvv)) (.classMem (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cvv)) p0020 p0025
  have p0027 :=
    @g_syl5eqel (.classMem A V) (syn_cimagek A) (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cvv) p0000 p0026
  exact p0027

noncomputable def g_imagekex
    (A : Class) (hyp_imagekex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cimagek A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_imagekexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_imagekex_1 p0000
  exact p0001

noncomputable def g_dfidk2
     :
    Nominal.NPrf (.classEq (syn_cidk) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk)))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_idkssvvk
  have p0001 :=
    @g_inss1 (syn_cssetk) (syn_ccnvk (syn_cssetk))
  have p0002 :=
    @g_ssetkssvvk
  have p0003 :=
    @g_sstri (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk))) (syn_cssetk) (syn_cxpk (syn_cvv) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_eqss (.cv x) (.cv y)
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_vex y
  have p0007 :=
    @g_opkelidkg (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0008_e02_recanon : Nominal.NPrf (.imp (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))) (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) (syn_cidk)) (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cvv syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cidk syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0007
  have p0008 :=
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) (syn_cidk)) (.objEq x y)) p0005 p0006 p0008_e02_recanon
  have p0009 :=
    @g_elin (syn_copk (.cv x) (.cv y)) (syn_cssetk) (syn_ccnvk (syn_cssetk))
  have p0010 :=
    @g_opkelssetkg (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) (syn_cssetk)) (syn_wss (.cv x) (.cv y))) p0005 p0006 p0010
  have p0012 :=
    @g_opkelcnvk (.cv x) (.cv y) (syn_cssetk) p0005 p0006
  have p0013 :=
    @g_opkelssetkg (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0014 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk)) (syn_wss (.cv y) (.cv x))) p0006 p0005 p0013
  have p0015 :=
    @g_bitri (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cssetk))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk)) (syn_wss (.cv y) (.cv x)) p0012 p0014
  have p0016 :=
    @g_anbi12i (.classMem (syn_copk (.cv x) (.cv y)) (syn_cssetk)) (syn_wss (.cv x) (.cv y)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cssetk))) (syn_wss (.cv y) (.cv x)) p0011 p0015
  have p0017 :=
    @g_bitri (.classMem (syn_copk (.cv x) (.cv y)) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk)))) (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_cssetk)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cssetk)))) (syn_wa (syn_wss (.cv x) (.cv y)) (syn_wss (.cv y) (.cv x))) p0009 p0016
  have p0018_e00_recanon : Nominal.NPrf (syn_wb (.objEq x y) (syn_wa (syn_wss (.cv x) (.cv y)) (syn_wss (.cv y) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0004
  have p0018 :=
    @g_n_3bitr4i (.objEq x y) (syn_wa (syn_wss (.cv x) (.cv y)) (syn_wss (.cv y) (.cv x))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cidk)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk)))) p0018_e00_recanon p0008 p0017
  have p0019 :=
    @g_eqrelkriiv x y (syn_cidk) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk))) (by exact (show x ∉ ((syn_cidk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((syn_cidk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ (((syn_cssetk)).fv) ∪ (((syn_ccnvk (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_ccnvk (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) (by exact (show y ∉ ((syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ (((syn_cssetk)).fv) ∪ (((syn_ccnvk (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_ccnvk (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) (show x ≠ y from (by exact fresh_x_ne_y)) p0000 p0003 p0018
  exact p0019

noncomputable def g_idkex
     :
    Nominal.NPrf (.classMem (syn_cidk) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_dfidk2
  have p0001 :=
    @g_ssetkex
  have p0002 :=
    @g_ssetkex
  have p0003 :=
    @g_cnvkex (syn_cssetk) p0002
  have p0004 :=
    @g_inex (syn_cssetk) (syn_ccnvk (syn_cssetk)) p0001 p0003
  have p0005 :=
    @g_eqeltri (syn_cidk) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk))) (syn_cvv) p0000 p0004
  exact p0005



#print axioms g_idkex

end NFChoice.DirectNominalPrf.WPPReplay
