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
import NominalWPPReplayChunk009StructuralPart007


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

noncomputable def g_opkelcokg
    (x : Var) (A : Class) (B : Class) (C : Class) (D : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_ccomk C D)) (syn_wex x (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ V.fv ∪ W.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_W : w ∉ W.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_w_ne_y : w ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have p0000 :=
    @g_elex A V
  have p0001 :=
    @g_elex B W
  have p0002 :=
    (by simpa [syn_ccomk] using (Nominal.classEqRefl (syn_ccomk C D)))
  have p0003 :=
    @g_eleq2i (syn_ccomk C D) (syn_cimak (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))) (syn_cvv)) (syn_copk A B) p0002
  have p0004 :=
    @g_opkex A B
  have p0005 :=
    @g_elimakv y (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))) (syn_copk A B) (by exact (show y ∉ ((syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ (((syn_cins2k C)).fv) ∪ (((syn_cins3k (syn_ccnvk D))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cins2k C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))) (show y ∉ ((syn_cins3k (syn_ccnvk D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show y ∉ ((syn_ccnvk D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show y ∉ (D).fv from (by exact fresh_y_not_D))))))))))) (by exact (show y ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) p0004
  have p0006 :=
    @g_vex y
  have p0007 :=
    @g_opkelins2kg x z w (.cv y) (syn_copk A B) C (syn_cvv) (syn_cvv) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y))))))) (by exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))) (by exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))) (by exact (show x ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ (B).fv from (by exact dv_B_x))))))) (by exact (show z ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))) (by exact (show w ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (A).fv from (by exact fresh_w_not_A)) (show w ∉ (B).fv from (by exact fresh_w_not_B))))))) (by exact (show x ∉ (C).fv from (by exact dv_C_x))) (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) (by exact (show w ∉ (C).fv from (by exact fresh_w_not_C))) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0008 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (syn_copk A B) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C)) (syn_wex x (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))))) p0006 p0004 p0007
  have p0009 :=
    @g_n_3anass (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)
  have p0010 :=
    @g_n_2exbii (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)) (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))) z w p0009
  have p0011 :=
    @g_n_19_42vv (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)) z w (by exact (show z ∉ ((Wff.classEq (.cv y) (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv y)).fv) ∪ (((syn_csn (syn_csn (.cv x)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))) (show z ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))))))))))) (by exact (show w ∉ ((Wff.classEq (.cv y) (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((syn_csn (syn_csn (.cv x)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))))))))))))
  have p0012 :=
    @g_bitri (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (syn_wex z (syn_wex w (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) p0010 p0011
  have p0013 :=
    @g_exbii (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) x p0012
  have p0014 :=
    @g_bitri (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C)) (syn_wex x (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))))) p0008 p0013
  have p0015 :=
    @g_anbi1i (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C)) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) p0014
  have p0016 :=
    @g_elin (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C) (syn_cins3k (syn_ccnvk D))
  have p0017 :=
    @g_n_19_41v (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) x (by exact (show x ∉ ((Wff.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk (.cv y) (syn_copk A B))).fv) ∪ (((syn_cins3k (syn_ccnvk D))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk (.cv y) (syn_copk A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((syn_copk A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ (B).fv from (by exact dv_B_x)))))))))) (show x ∉ ((syn_cins3k (syn_ccnvk D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ ((syn_ccnvk D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show x ∉ (D).fv from (by exact dv_D_x)))))))))))
  have p0018 :=
    @g_n_3bitr4i (syn_wa (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C)) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) (syn_wa (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D)))) (syn_wex x (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))) p0015 p0016 p0017
  have p0019 :=
    @g_exbii (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D)))) (syn_wex x (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))) y p0018
  have p0020 :=
    @g_excom (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) y x
  have p0021 :=
    @g_anass (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))
  have p0022 :=
    @g_exbii (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))) y p0021
  have p0023 :=
    @g_snex (syn_csn (.cv x))
  have p0024 :=
    @g_opkeq1 (.cv y) (syn_csn (syn_csn (.cv x))) (syn_copk A B)
  have p0025 :=
    @g_eleq1d (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv y) (syn_copk A B)) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)) p0024
  have p0026 :=
    @g_anbi2d (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) p0025
  have p0027 :=
    @g_ceqsexv (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) y (syn_csn (syn_csn (.cv x))) (by exact (show y ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))) (by exact (show y ∉ ((syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))).fv) ∪ (((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show y ∉ (((syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))).fv).erase z from (fun hmem => (show y ∉ ((syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show y ∉ (((syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))).fv).erase w from (fun hmem => (show y ∉ ((syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))).fv) ∪ (((Wff.classMem (syn_copk (.cv x) (.cv w)) C)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((syn_copk A B)).fv) ∪ (((syn_copk (.cv z) (.cv w))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B)))))) (show y ∉ ((syn_copk (.cv z) (.cv w))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((Class.cv z)).fv) ∪ (((Class.cv w)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))))))))))) (show y ∉ ((Wff.classMem (syn_copk (.cv x) (.cv w)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk (.cv x) (.cv w))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk (.cv x) (.cv w))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((Class.cv w)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))))))) (show y ∉ (C).fv from (by exact fresh_y_not_C)))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem))))) (show y ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))).fv) ∪ (((syn_cins3k (syn_ccnvk D))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((syn_csn (syn_csn (.cv x)))).fv) ∪ (((syn_copk A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))) (show y ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B)))))))))) (show y ∉ ((syn_cins3k (syn_ccnvk D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show y ∉ ((syn_ccnvk D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show y ∉ (D).fv from (by exact fresh_y_not_D))))))))))))))) p0023 p0026
  have p0028 :=
    @g_bitri (syn_wex y (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))) (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))))) (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) p0022 p0027
  have p0029 :=
    @g_exbii (syn_wex y (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))) (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) x p0028
  have p0030 :=
    @g_n_3bitri (syn_wex y (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))))) (syn_wex y (syn_wex x (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))))) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))))) (syn_wex x (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))) p0019 p0020 p0029
  have p0031 :=
    @g_n_3bitri (.classMem (syn_copk A B) (syn_ccomk C D)) (.classMem (syn_copk A B) (syn_cimak (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))) (syn_cvv))) (syn_wex y (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))))) (syn_wex x (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))) p0003 p0005 p0030
  have p0032 :=
    @g_ancom (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))
  have p0033 :=
    @g_vex x
  have p0034 :=
    @g_otkelins3kg (.cv x) A B (syn_ccnvk D) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0035 :=
    @g_mp3an1 (.classMem (.cv x) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) (.classMem (syn_copk (.cv x) A) (syn_ccnvk D))) p0033 p0034
  have p0036 :=
    @g_opkelcnvkg (.cv x) A D (syn_cvv) (syn_cvv)
  have p0037 :=
    @g_mpan (.classMem (.cv x) (syn_cvv)) (.classMem A (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv x) A) (syn_ccnvk D)) (.classMem (syn_copk A (.cv x)) D)) p0033 p0036
  have p0038 :=
    @g_adantr (.classMem A (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv x) A) (syn_ccnvk D)) (.classMem (syn_copk A (.cv x)) D)) (.classMem B (syn_cvv)) p0037
  have p0039 :=
    @g_bitrd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) (.classMem (syn_copk (.cv x) A) (syn_ccnvk D)) (.classMem (syn_copk A (.cv x)) D) p0035 p0038
  have p0040 :=
    @g_eqcom (syn_copk A B) (syn_copk (.cv z) (.cv w))
  have p0041 :=
    @g_anbi1i (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B)) (.classMem (syn_copk (.cv x) (.cv w)) C) p0040
  have p0042 :=
    @g_n_2exbii (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)) (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B)) (.classMem (syn_copk (.cv x) (.cv w)) C)) z w p0041
  have p0043 :=
    @g_vex z
  have p0044 :=
    @g_vex w
  have p0045 :=
    @g_opkthg (.cv z) (.cv w) A B (syn_cvv) (syn_cvv) (syn_cvv)
  have p0046 :=
    @g_mp3an12 (.classMem (.cv z) (syn_cvv)) (.classMem (.cv w) (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B)) (syn_wa (.classEq (.cv z) A) (.classEq (.cv w) B))) p0043 p0044 p0045
  have p0047 :=
    @g_anbi1d (.classMem B (syn_cvv)) (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B)) (syn_wa (.classEq (.cv z) A) (.classEq (.cv w) B)) (.classMem (syn_copk (.cv x) (.cv w)) C) p0046
  have p0048 :=
    @g_anass (.classEq (.cv z) A) (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)
  have p0049 :=
    @g_syl6bb (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B)) (.classMem (syn_copk (.cv x) (.cv w)) C)) (syn_wa (syn_wa (.classEq (.cv z) A) (.classEq (.cv w) B)) (.classMem (syn_copk (.cv x) (.cv w)) C)) (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))) p0047 p0048
  have p0050 :=
    @g_n_2exbidv (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B)) (.classMem (syn_copk (.cv x) (.cv w)) C)) (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))) z w (by exact (show z ∉ ((Wff.classMem B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (B).fv from (by exact fresh_z_not_B)) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show w ∉ ((Wff.classMem B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (B).fv from (by exact fresh_w_not_B)) (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0049
  have p0051 :=
    @g_adantl (.classMem B (syn_cvv)) (syn_wb (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B)) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (syn_wex z (syn_wex w (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))))) (.classMem A (syn_cvv)) p0050
  have p0052 :=
    @g_eeanv (.classEq (.cv z) A) (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)) z w (by exact (show w ∉ ((Wff.classEq (.cv z) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv z)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))) (show w ∉ (A).fv from (by exact fresh_w_not_A))))))) (by exact (show z ∉ ((syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show z ∉ (((Wff.classEq (.cv w) B)).fv) ∪ (((Wff.classMem (syn_copk (.cv x) (.cv w)) C)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classEq (.cv w) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv w)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ w from (by exact fresh_z_ne_w)))))) (show z ∉ (B).fv from (by exact fresh_z_not_B)))))) (show z ∉ ((Wff.classMem (syn_copk (.cv x) (.cv w)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (.cv x) (.cv w))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (.cv x) (.cv w))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv w)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ w from (by exact fresh_z_ne_w)))))))))) (show z ∉ (C).fv from (by exact fresh_z_not_C)))))))))))
  have p0053 :=
    @g_syl6bb (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B)) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (syn_wex z (syn_wex w (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))) p0051 p0052
  have p0054 :=
    @g_syl5bb (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B)) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))) p0042 p0053
  have p0055 :=
    @g_elisset z A (syn_cvv) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
  have p0056 :=
    @g_biantrurd (.classMem A (syn_cvv)) (syn_wex z (.classEq (.cv z) A)) (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))) p0055
  have p0057 :=
    @g_bicomd (.classMem A (syn_cvv)) (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))) (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))) p0056
  have p0058 :=
    @g_opkeq2 (.cv w) B (.cv x)
  have p0059 :=
    @g_eleq1d (.classEq (.cv w) B) (syn_copk (.cv x) (.cv w)) (syn_copk (.cv x) B) C p0058
  have p0060 :=
    @g_ceqsexgv (.classMem (syn_copk (.cv x) (.cv w)) C) (.classMem (syn_copk (.cv x) B) C) w B (syn_cvv) (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) (by exact (show w ∉ ((Wff.classMem (syn_copk (.cv x) B) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((syn_copk (.cv x) B)).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_copk (.cv x) B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv x)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))) (show w ∉ (B).fv from (by exact fresh_w_not_B)))))) (show w ∉ (C).fv from (by exact fresh_w_not_C))))))) p0059
  have p0061 :=
    @g_sylan9bb (.classMem A (syn_cvv)) (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))) (.classMem B (syn_cvv)) (.classMem (syn_copk (.cv x) B) C) p0057 p0060
  have p0062 :=
    @g_bitrd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (.cv x) B) C) p0054 p0061
  have p0063 :=
    @g_anbi12d (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) (.classMem (syn_copk A (.cv x)) D) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (.cv x) B) C) p0039 p0062
  have p0064 :=
    @g_syl5bb (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C))))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C)) p0032 p0063
  have p0065 :=
    @g_exbidv (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))) (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C)) x (by exact (show x ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classMem A (syn_cvv))).fv) ∪ (((Wff.classMem B (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.classMem B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact dv_B_x)) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0064
  have p0066 :=
    @g_syl5bb (.classMem (syn_copk A B) (syn_ccomk C D)) (syn_wex x (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w))) (.classMem (syn_copk (.cv x) (.cv w)) C)))) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wex x (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C))) p0031 p0065
  have p0067 :=
    @g_syl2an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk A B) (syn_ccomk C D)) (syn_wex x (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C)))) (.classMem B W) p0000 p0001 p0066
  exact p0067

noncomputable def g_opkelcok
    (x : Var) (A : Class) (B : Class) (C : Class) (D : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) (hyp_opkelcok_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_opkelcok_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk A B) (syn_ccomk C D)) (syn_wex x (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_opkelcokg x A B C D (syn_cvv) (syn_cvv) (by exact (show x ∉ (A).fv from (by exact dv_A_x))) (by exact (show x ∉ (B).fv from (by exact dv_B_x))) (by exact (show x ∉ (C).fv from (by exact dv_C_x))) (by exact (show x ∉ (D).fv from (by exact dv_D_x)))
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk A B) (syn_ccomk C D)) (syn_wex x (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C)))) hyp_opkelcok_1 hyp_opkelcok_2 p0000
  exact p0001

noncomputable def g_elp6
    (x : Var) (A : Class) (B : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classMem A (syn_cp6 B)) (.all x (.classMem (syn_copk (.cv x) (syn_csn A)) B)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_sneq (.cv y) A
  have p0001 :=
    @g_sneqd (.classEq (.cv y) A) (syn_csn (.cv y)) (syn_csn A) p0000
  have p0002 :=
    @g_xpkeq2d (.classEq (.cv y) A) (syn_csn (syn_csn (.cv y))) (syn_csn (syn_csn A)) (syn_cvv) p0001
  have p0003 :=
    @g_sseq1d (.classEq (.cv y) A) (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv y)))) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_p6 y B (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0005 :=
    @g_elab2g (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv y)))) B) (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B) y A (syn_cp6 B) V (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ ((syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show y ∉ (((syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cvv)).fv) ∪ (((syn_csn (syn_csn A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))))))) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) p0003 p0004
  have p0006 :=
    @g_xpkssvvk (syn_cvv) (syn_csn (syn_csn A))
  have p0007 :=
    @g_ssrelk x y (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B (by exact (show x ∉ ((syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ (((syn_cvv)).fv) ∪ (((syn_csn (syn_csn A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (A).fv from (by exact dv_A_x))))))))))) (by exact (show y ∉ ((syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cvv)).fv) ∪ (((syn_csn (syn_csn A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))))))))) (by exact (show x ∉ (B).fv from (by exact dv_B_x))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_vex x
  have p0010 :=
    @g_vex y
  have p0011 :=
    @g_opkelxpk (.cv x) (.cv y) (syn_cvv) (syn_csn (syn_csn A)) p0009 p0010
  have p0012 :=
    @g_biantrur (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_csn (syn_csn A))) p0009
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn y (syn_csn A) (by exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
  have p0014 :=
    @g_eqabri (.classEq (.cv y) (syn_csn A)) y (syn_csn (syn_csn A)) p0013
  have p0015 :=
    @g_n_3bitr2i (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_csn (syn_csn A)))) (.classMem (.cv y) (syn_csn (syn_csn A))) (.classEq (.cv y) (syn_csn A)) p0011 p0012 p0014
  have p0016 :=
    @g_imbi1i (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))) (.classEq (.cv y) (syn_csn A)) (.classMem (syn_copk (.cv x) (.cv y)) B) p0015
  have p0017 :=
    @g_albii (.imp (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))) (.classMem (syn_copk (.cv x) (.cv y)) B)) (.imp (.classEq (.cv y) (syn_csn A)) (.classMem (syn_copk (.cv x) (.cv y)) B)) y p0016
  have p0018 :=
    @g_snex A
  have p0019 :=
    @g_opkeq2 (.cv y) (syn_csn A) (.cv x)
  have p0020 :=
    @g_eleq1d (.classEq (.cv y) (syn_csn A)) (syn_copk (.cv x) (.cv y)) (syn_copk (.cv x) (syn_csn A)) B p0019
  have p0021 :=
    @g_ceqsalv (.classMem (syn_copk (.cv x) (.cv y)) B) (.classMem (syn_copk (.cv x) (syn_csn A)) B) y (syn_csn A) (by exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))) (by exact (show y ∉ ((Wff.classMem (syn_copk (.cv x) (syn_csn A)) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk (.cv x) (syn_csn A))).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk (.cv x) (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_csn A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))))) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) p0018 p0020
  have p0022 :=
    @g_bitri (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))) (.classMem (syn_copk (.cv x) (.cv y)) B))) (.all y (.imp (.classEq (.cv y) (syn_csn A)) (.classMem (syn_copk (.cv x) (.cv y)) B))) (.classMem (syn_copk (.cv x) (syn_csn A)) B) p0017 p0021
  have p0023 :=
    @g_albii (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))) (.classMem (syn_copk (.cv x) (.cv y)) B))) (.classMem (syn_copk (.cv x) (syn_csn A)) B) x p0022
  have p0024 :=
    @g_bitri (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B) (.all x (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))) (.classMem (syn_copk (.cv x) (.cv y)) B)))) (.all x (.classMem (syn_copk (.cv x) (syn_csn A)) B)) p0008 p0023
  have p0025 :=
    @g_syl6bb (.classMem A V) (.classMem A (syn_cp6 B)) (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B) (.all x (.classMem (syn_copk (.cv x) (syn_csn A)) B)) p0005 p0024
  exact p0025



#print axioms g_elp6

end NFChoice.DirectNominalPrf.WPPReplay
