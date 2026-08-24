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
import NominalWPPReplayChunk009StructuralPart035


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

noncomputable def g_nnceleq
    (A : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem A N))) (.classEq M N)) := by
  let proofSupport : Finset Var := A.fv ∪ M.fv ∪ N.fv
  have p0000 :=
    @g_elin A M N
  have p0001 :=
    @g_n0i (syn_cin M N) A
  have p0002 :=
    @g_sylbir (syn_wa (.classMem A M) (.classMem A N)) (.classMem A (syn_cin M N)) (.neg (.classEq (syn_cin M N) (syn_c0))) p0000 p0001
  have p0003 :=
    @g_adantl (syn_wa (.classMem A M) (.classMem A N)) (.neg (.classEq (syn_cin M N) (syn_c0))) (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) p0002
  have p0004 :=
    @g_nndisjeq M N
  have p0005 :=
    @g_adantr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)) (syn_wa (.classMem A M) (.classMem A N)) p0004
  have p0006 :=
    @g_orel1 (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)
  have p0007 :=
    @g_sylc (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem A N))) (.neg (.classEq (syn_cin M N) (syn_c0))) (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)) (.classEq M N) p0003 p0005 p0006
  exact p0007

noncomputable def g_opklefing
    (x : Var) (A : Class) (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_W : w ∉ W.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lefin w y z x (show x ≠ w from (by exact fresh_x_ne_w)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_addceq1 (.cv y) A (.cv x)
  have p0002 :=
    @g_eqeq2d (.classEq (.cv y) A) (syn_cplc (.cv y) (.cv x)) (syn_cplc A (.cv x)) (.cv z) p0001
  have p0003 :=
    @g_rexbidv (.classEq (.cv y) A) (.classEq (.cv z) (syn_cplc (.cv y) (.cv x))) (.classEq (.cv z) (syn_cplc A (.cv x))) x (syn_cnnc) (by exact (show x ∉ ((Wff.classEq (.cv y) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv y)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ (A).fv from (by exact dv_A_x))))))) p0002
  have p0004 :=
    @g_eqeq1 (.cv z) B (syn_cplc A (.cv x))
  have p0005 :=
    @g_rexbidv (.classEq (.cv z) B) (.classEq (.cv z) (syn_cplc A (.cv x))) (.classEq B (syn_cplc A (.cv x))) x (syn_cnnc) (by exact (show x ∉ ((Wff.classEq (.cv z) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv z)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ (B).fv from (by exact dv_B_x))))))) p0004
  have p0006 :=
    @g_opkelopkabg (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv y) (.cv x)))) (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc A (.cv x)))) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) w y z (syn_clefin) A B V W (by exact (show y ∉ ((syn_clefin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show z ∉ ((syn_clefin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show z ∉ ((syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show z ∉ ((((syn_cnnc)).fv).erase x) ∪ ((((Wff.classEq B (syn_cplc A (.cv x)))).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (((syn_cnnc)).fv).erase x from (fun hmem => (show z ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show z ∉ (((Wff.classEq B (syn_cplc A (.cv x)))).fv).erase x from (fun hmem => (show z ∉ ((Wff.classEq B (syn_cplc A (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ ((B).fv) ∪ (((syn_cplc A (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (B).fv from (by exact fresh_z_not_B)) (show z ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show w ∉ ((syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv y) (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show w ∉ ((((syn_cnnc)).fv).erase x) ∪ ((((Wff.classEq (.cv z) (syn_cplc (.cv y) (.cv x)))).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (((syn_cnnc)).fv).erase x from (fun hmem => (show w ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show w ∉ (((Wff.classEq (.cv z) (syn_cplc (.cv y) (.cv x)))).fv).erase x from (fun hmem => (show w ∉ ((Wff.classEq (.cv z) (syn_cplc (.cv y) (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv z)).fv) ∪ (((syn_cplc (.cv y) (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))) (show w ∉ ((syn_cplc (.cv y) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show y ∉ ((syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc A (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show y ∉ ((((syn_cnnc)).fv).erase x) ∪ ((((Wff.classEq (.cv z) (syn_cplc A (.cv x)))).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (((syn_cnnc)).fv).erase x from (fun hmem => (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show y ∉ (((Wff.classEq (.cv z) (syn_cplc A (.cv x)))).fv).erase x from (fun hmem => (show y ∉ ((Wff.classEq (.cv z) (syn_cplc A (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv z)).fv) ∪ (((syn_cplc A (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z)) p0000 p0003 p0005
  exact p0006

noncomputable def g_opkltfing
    (x : Var) (A : Class) (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
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
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
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
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ltfin y z w x (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y)) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 :=
    @g_neeq1 (.cv z) A (syn_c0)
  have p0002 :=
    @g_addceq1 (.cv z) A (.cv x)
  have p0003 :=
    @g_addceq1d (.classEq (.cv z) A) (syn_cplc (.cv z) (.cv x)) (syn_cplc A (.cv x)) (syn_c1c) p0002
  have p0004 :=
    @g_eqeq2d (.classEq (.cv z) A) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv w) p0003
  have p0005 :=
    @g_rexbidv (.classEq (.cv z) A) (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c))) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) x (syn_cnnc) (by exact (show x ∉ ((Wff.classEq (.cv z) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv z)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ (A).fv from (by exact dv_A_x))))))) p0004
  have p0006 :=
    @g_anbi12d (.classEq (.cv z) A) (syn_wne (.cv z) (syn_c0)) (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c)))) (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) p0001 p0005
  have p0007 :=
    @g_eqeq1 (.cv w) B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))
  have p0008 :=
    @g_rexbidv (.classEq (.cv w) B) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) x (syn_cnnc) (by exact (show x ∉ ((Wff.classEq (.cv w) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv w)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ w from (by exact fresh_x_ne_w)))))) (show x ∉ (B).fv from (by exact dv_B_x))))))) p0007
  have p0009 :=
    @g_anbi2d (.classEq (.cv w) B) (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) (syn_wne A (syn_c0)) p0008
  have p0010 :=
    @g_opkelopkabg (syn_wa (syn_wne (.cv z) (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c))))) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) y z w (syn_cltfin) A B V W (by exact (show z ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show w ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) (by exact (show w ∉ ((syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show w ∉ (((syn_wne A (syn_c0))).fv) ∪ (((syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_wne A (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show w ∉ ((A).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (A).fv from (by exact fresh_w_not_A)) (show w ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show w ∉ ((syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show w ∉ ((((syn_cnnc)).fv).erase x) ∪ ((((Wff.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (((syn_cnnc)).fv).erase x from (fun hmem => (show w ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show w ∉ (((Wff.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))).fv).erase x from (fun hmem => (show w ∉ ((Wff.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ ((B).fv) ∪ (((syn_cplc (syn_cplc A (.cv x)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (B).fv from (by exact fresh_w_not_B)) (show w ∉ ((syn_cplc (syn_cplc A (.cv x)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show w ∉ (((syn_cplc A (.cv x))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show w ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (A).fv from (by exact fresh_w_not_A)) (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))))))) (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem)))))))))))) (by exact (show y ∉ ((syn_wa (syn_wne (.cv z) (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((syn_wne (.cv z) (syn_c0))).fv) ∪ (((syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_wne (.cv z) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show y ∉ (((Class.cv z)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show y ∉ ((syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show y ∉ ((((syn_cnnc)).fv).erase x) ∪ ((((Wff.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c)))).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (((syn_cnnc)).fv).erase x from (fun hmem => (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show y ∉ (((Wff.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c)))).fv).erase x from (fun hmem => (show y ∉ ((Wff.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv w)).fv) ∪ (((syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))) (show y ∉ ((syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((syn_cplc (.cv z) (.cv x))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cplc (.cv z) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((Class.cv z)).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem)))))))))))) (by exact (show z ∉ ((syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show z ∉ (((syn_wne A (syn_c0))).fv) ∪ (((syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_wne A (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show z ∉ ((A).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show z ∉ ((syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show z ∉ ((((syn_cnnc)).fv).erase x) ∪ ((((Wff.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (((syn_cnnc)).fv).erase x from (fun hmem => (show z ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show z ∉ (((Wff.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))).fv).erase x from (fun hmem => (show z ∉ ((Wff.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv w)).fv) ∪ (((syn_cplc (syn_cplc A (.cv x)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ w from (by exact fresh_z_ne_w)))))) (show z ∉ ((syn_cplc (syn_cplc A (.cv x)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_cplc A (.cv x))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem)))))))))))) (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w)) p0000 p0006 p0009
  exact p0010

noncomputable def g_lefinaddc
    (A : Class) (N : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem N (syn_cnnc))) (.classMem (syn_copk A (syn_cplc A N)) (syn_clefin))) := by
  let proofSupport : Finset Var := A.fv ∪ N.fv ∪ V.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_V : n ∉ V.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eqid (syn_cplc A N)
  have p0001 :=
    @g_addceq2 (.cv n) N A
  have p0002 :=
    @g_eqeq2d (.classEq (.cv n) N) (syn_cplc A (.cv n)) (syn_cplc A N) (syn_cplc A N) p0001
  have p0003 :=
    @g_rspcev (.classEq (syn_cplc A N) (syn_cplc A (.cv n))) (.classEq (syn_cplc A N) (syn_cplc A N)) n N (syn_cnnc) (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N))) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((Wff.classEq (syn_cplc A N) (syn_cplc A N))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((syn_cplc A N)).fv) ∪ (((syn_cplc A N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cplc A N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show n ∉ ((A).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (A).fv from (by exact fresh_n_not_A)) (show n ∉ (N).fv from (by exact fresh_n_not_N)))))) (show n ∉ ((syn_cplc A N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show n ∉ ((A).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (A).fv from (by exact fresh_n_not_A)) (show n ∉ (N).fv from (by exact fresh_n_not_N))))))))))) p0002
  have p0004 :=
    @g_mpan2 (.classMem N (syn_cnnc)) (.classEq (syn_cplc A N) (syn_cplc A N)) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc A N) (syn_cplc A (.cv n)))) p0000 p0003
  have p0005 :=
    @g_adantl (.classMem N (syn_cnnc)) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc A N) (syn_cplc A (.cv n)))) (.classMem A V) p0004
  have p0006 :=
    @g_addcexg A N V (syn_cnnc)
  have p0007 :=
    @g_opklefing n A (syn_cplc A N) V (syn_cvv) (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A))) (by exact (show n ∉ ((syn_cplc A N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show n ∉ ((A).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (A).fv from (by exact fresh_n_not_A)) (show n ∉ (N).fv from (by exact fresh_n_not_N)))))))
  have p0008 :=
    @g_syldan (.classMem A V) (.classMem N (syn_cnnc)) (.classMem (syn_cplc A N) (syn_cvv)) (syn_wb (.classMem (syn_copk A (syn_cplc A N)) (syn_clefin)) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc A N) (syn_cplc A (.cv n))))) p0006 p0007
  have p0009 :=
    @g_mpbird (syn_wa (.classMem A V) (.classMem N (syn_cnnc))) (.classMem (syn_copk A (syn_cplc A N)) (syn_clefin)) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc A N) (syn_cplc A (.cv n)))) p0005 p0008
  exact p0009

noncomputable def g_prepeano4
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)))) (.classEq M N)) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have p0000 :=
    @g_n0 a (syn_cplc M (syn_c1c)) (by exact (show a ∉ ((syn_cplc M (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((M).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))
  have p0001 :=
    @g_elsuc x (.cv a) M b (by exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a))))))) (by exact (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a))))))) (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) (show b ≠ x from (by exact fresh_b_ne_x))
  have p0002 :=
    @g_simplll (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))
  have p0003 :=
    @g_simpllr (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))
  have p0004 :=
    @g_simprl (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))
  have p0005 :=
    @g_simprr (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_elcompl (.cv x) (.cv b) p0006
  have p0008_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b))) :=
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
  have p0008 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b)) p0005 p0008_e01_recanon
  have p0009 :=
    @g_elsuci (.cv b) M (.cv x) p0006
  have p0010_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b))) :=
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
  have p0010_e01_recanon : Nominal.NPrf (.imp (syn_wa (.classMem (.cv b) M) (.neg (.objMem x b))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_sylan2b (.classMem (.cv x) (syn_ccompl (.cv b))) (.classMem (.cv b) M) (.neg (.objMem x b)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))) p0010_e00_recanon p0010_e01_recanon
  have p0011 :=
    @g_adantl (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) p0010
  have p0012 :=
    @g_simplr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))
  have p0013 :=
    @g_eleqtrd (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)) p0011 p0012
  have p0014 :=
    @g_vex b
  have p0015 :=
    @g_nnsucelr (.cv b) N (.cv x) p0014 p0006
  have p0016_e03_recanon : Nominal.NPrf (.imp (syn_wa (.classMem N (syn_cnnc)) (syn_wa (.neg (.objMem x b)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc N (syn_c1c))))) (.classMem (.cv b) N)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0015
  have p0016 :=
    @g_syl12anc (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (.classMem N (syn_cnnc)) (.neg (.objMem x b)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc N (syn_c1c))) (.classMem (.cv b) N) p0003 p0008 p0013 p0016_e03_recanon
  have p0017 :=
    @g_nnceleq (.cv b) M N
  have p0018 :=
    @g_syl22anc (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (.cv b) M) (.classMem (.cv b) N) (.classEq M N) p0002 p0003 p0004 p0016 p0017
  have p0019 :=
    @g_a1d (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (.classEq M N) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) p0018
  have p0020 :=
    @g_rexlimdvva (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.classEq M N) b x M (syn_ccompl (.cv b)) (by exact (show x ∉ (M).fv from (by exact fresh_x_not_M))) (by exact (show b ∉ ((Wff.classEq M N)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (M).fv from (by exact fresh_b_not_M)) (show b ∉ (N).fv from (by exact fresh_b_not_N))))))) (by exact (show x ∉ ((Wff.classEq M N)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (M).fv from (by exact fresh_x_not_M)) (show x ∉ (N).fv from (by exact fresh_x_not_N))))))) (by exact (show b ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv) ∪ (((Wff.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (M).fv from (by exact fresh_b_not_M)) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (N).fv from (by exact fresh_b_not_N)) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show b ∉ ((Wff.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((syn_cplc M (syn_c1c))).fv) ∪ (((syn_cplc N (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cplc M (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ ((M).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (M).fv from (by exact fresh_b_not_M)) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((syn_cplc N (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ ((N).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (N).fv from (by exact fresh_b_not_N)) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) (by exact (show x ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv) ∪ (((Wff.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (M).fv from (by exact fresh_x_not_M)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (N).fv from (by exact fresh_x_not_N)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show x ∉ ((Wff.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_cplc M (syn_c1c))).fv) ∪ (((syn_cplc N (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cplc M (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((M).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (M).fv from (by exact fresh_x_not_M)) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((syn_cplc N (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((N).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (N).fv from (by exact fresh_x_not_N)) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) (show b ≠ x from (by exact fresh_b_ne_x)) p0019
  have p0021 :=
    @g_syl5bi (.classMem (.cv a) (syn_cplc M (syn_c1c))) (syn_wrex b M (syn_wrex x (syn_ccompl (.cv b)) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))))) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (.classEq M N) p0001 p0020
  have p0022 :=
    @g_exlimdv (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (.classMem (.cv a) (syn_cplc M (syn_c1c))) (.classEq M N) a (by exact (show a ∉ ((Wff.classEq M N)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ (N).fv from (by exact fresh_a_not_N))))))) (by exact (show a ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv) ∪ (((Wff.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (N).fv from (by exact fresh_a_not_N)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show a ∉ ((Wff.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_cplc M (syn_c1c))).fv) ∪ (((syn_cplc N (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cplc M (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((M).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((syn_cplc N (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((N).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (N).fv from (by exact fresh_a_not_N)) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0021
  have p0023 :=
    @g_syl5bi (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)) (syn_wex a (.classMem (.cv a) (syn_cplc M (syn_c1c)))) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (.classEq M N) p0000 p0022
  have p0024 :=
    @g_impr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)) (.classEq M N) p0023
  exact p0024



#print axioms g_prepeano4

end NFChoice.DirectNominalPrf.WPPReplay
