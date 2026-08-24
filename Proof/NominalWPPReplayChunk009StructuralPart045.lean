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
import NominalWPPReplayChunk009StructuralPart044


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

noncomputable def g_lefinrflx
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_copk A A) (syn_clefin))) := by
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
    @g_peano1
  have p0001 :=
    @g_addcid1 A
  have p0002 :=
    @g_eqcomi (syn_cplc A (syn_c0c)) A p0001
  have p0003 :=
    @g_addceq2 (.cv x) (syn_c0c) A
  have p0004 :=
    @g_eqeq2d (.classEq (.cv x) (syn_c0c)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0c)) A p0003
  have p0005 :=
    @g_rspcev (.classEq A (syn_cplc A (.cv x))) (.classEq A (syn_cplc A (syn_c0c))) x (syn_c0c) (syn_cnnc) (by exact (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((Wff.classEq A (syn_cplc A (syn_c0c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((syn_cplc A (syn_c0c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cplc A (syn_c0c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0004
  have p0006 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classEq A (syn_cplc A (syn_c0c))) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x)))) p0000 p0002 p0005
  have p0007 :=
    @g_opklefing x A A V V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0008 :=
    @g_anidms (.classMem A V) (syn_wb (.classMem (syn_copk A A) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x))))) p0007
  have p0009 :=
    @g_mpbiri (.classMem A V) (.classMem (syn_copk A A) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x)))) p0006 p0008
  exact p0009

noncomputable def g_ltlefin
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.imp (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk A B) (syn_clefin)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_addcass A (.cv x) (syn_c1c)
  have p0001 :=
    @g_eqeq2i (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (syn_cplc A (syn_cplc (.cv x) (syn_c1c))) B p0000
  have p0002 :=
    @g_peano2 (.cv x)
  have p0003 :=
    @g_addceq2 (.cv y) (syn_cplc (.cv x) (syn_c1c)) A
  have p0004 :=
    @g_eqeq2d (.classEq (.cv y) (syn_cplc (.cv x) (syn_c1c))) (syn_cplc A (.cv y)) (syn_cplc A (syn_cplc (.cv x) (syn_c1c))) B p0003
  have p0005 :=
    @g_rspcev (.classEq B (syn_cplc A (.cv y))) (.classEq B (syn_cplc A (syn_cplc (.cv x) (syn_c1c)))) y (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc) (by exact (show y ∉ ((syn_cplc (.cv x) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((Wff.classEq B (syn_cplc A (syn_cplc (.cv x) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((B).fv) ∪ (((syn_cplc A (syn_cplc (.cv x) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ ((syn_cplc A (syn_cplc (.cv x) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ ((A).fv) ∪ (((syn_cplc (.cv x) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((syn_cplc (.cv x) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0004
  have p0006 :=
    @g_sylan (.classMem (.cv x) (syn_cnnc)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)) (.classEq B (syn_cplc A (syn_cplc (.cv x) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))) p0002 p0005
  have p0007 :=
    @g_sylan2b (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classMem (.cv x) (syn_cnnc)) (.classEq B (syn_cplc A (syn_cplc (.cv x) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))) p0001 p0006
  have p0008 :=
    @g_rexlimiva (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))) x (syn_cnnc) (by exact (show x ∉ ((syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show x ∉ ((((syn_cnnc)).fv).erase y) ∪ ((((Wff.classEq B (syn_cplc A (.cv y)))).fv).erase y) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (((syn_cnnc)).fv).erase y from (fun hmem => (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show x ∉ (((Wff.classEq B (syn_cplc A (.cv y)))).fv).erase y from (fun hmem => (show x ∉ ((Wff.classEq B (syn_cplc A (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((B).fv) ∪ (((syn_cplc A (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ ((syn_cplc A (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))))))) (Finset.mem_of_mem_erase hmem)))))))) p0007
  have p0009 :=
    @g_adantl (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))) (syn_wne A (syn_c0)) p0008
  have p0010 :=
    @g_a1i (.imp (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y))))) (syn_wa (.classMem A V) (.classMem B W)) p0009
  have p0011 :=
    @g_opkltfing x A B V W (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0012 :=
    @g_opklefing y A B V W (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0013 :=
    @g_n_3imtr4d (syn_wa (.classMem A V) (.classMem B W)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))) (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk A B) (syn_clefin)) p0010 p0011 p0012
  exact p0013

noncomputable def g_lenltfin
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (.neg (.classMem (syn_copk B A) (syn_cltfin))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_ltfinirr A
  have p0001 :=
    @g_adantr (.classMem A (syn_cnnc)) (.neg (.classMem (syn_copk A A) (syn_cltfin))) (.classMem B (syn_cnnc)) p0000
  have p0002 :=
    @g_adantr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.neg (.classMem (syn_copk A A) (syn_cltfin))) (.classMem (syn_copk A B) (syn_clefin)) p0001
  have p0003 :=
    @g_leltfintr A B A
  have p0004 :=
    @g_n_3anidm13 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.imp (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_cltfin))) (.classMem (syn_copk A A) (syn_cltfin))) p0003
  have p0005 :=
    @g_expdimp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk A A) (syn_cltfin)) p0004
  have p0006 :=
    @g_mtod (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin))) (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk A A) (syn_cltfin)) p0002 p0005
  have p0007 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin)) (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0006
  have p0008 :=
    @g_nulge A (syn_cnnc)
  have p0009 :=
    @g_ancoms (.classMem (syn_c0) (syn_cnnc)) (.classMem A (syn_cnnc)) (.classMem (syn_copk A (syn_c0)) (syn_clefin)) p0008
  have p0010 :=
    @g_eleq1 B (syn_c0) (syn_cnnc)
  have p0011 :=
    @g_anbi2d (.classEq B (syn_c0)) (.classMem B (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc)) (.classMem A (syn_cnnc)) p0010
  have p0012 :=
    @g_opkeq2 B (syn_c0) A
  have p0013 :=
    @g_eleq1d (.classEq B (syn_c0)) (syn_copk A B) (syn_copk A (syn_c0)) (syn_clefin) p0012
  have p0014 :=
    @g_imbi12d (.classEq B (syn_c0)) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem A (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk A (syn_c0)) (syn_clefin)) p0011 p0013
  have p0015 :=
    @g_mpbiri (.classEq B (syn_c0)) (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin))) (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc))) (.classMem (syn_copk A (syn_c0)) (syn_clefin))) p0009 p0014
  have p0016 :=
    @g_a1dd (.classEq B (syn_c0)) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin)) (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0015
  have p0017 :=
    @g_simplr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wne B (syn_c0))
  have p0018 :=
    @g_simpll (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wne B (syn_c0))
  have p0019 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0))
  have p0020 :=
    @g_ltfintri B A
  have p0021 :=
    @g_syl3anc (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0))) (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)) (syn_wne B (syn_c0)) (syn_w3o (.classMem (syn_copk B A) (syn_cltfin)) (.classEq B A) (.classMem (syn_copk A B) (syn_cltfin))) p0017 p0018 p0019 p0020
  have p0022 :=
    @g_n_3orass (.classMem (syn_copk B A) (syn_cltfin)) (.classEq B A) (.classMem (syn_copk A B) (syn_cltfin))
  have p0023 :=
    @g_sylib (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0))) (syn_w3o (.classMem (syn_copk B A) (syn_cltfin)) (.classEq B A) (.classMem (syn_copk A B) (syn_cltfin))) (syn_wo (.classMem (syn_copk B A) (syn_cltfin)) (syn_wo (.classEq B A) (.classMem (syn_copk A B) (syn_cltfin)))) p0021 p0022
  have p0024 :=
    @g_ord (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0))) (.classMem (syn_copk B A) (syn_cltfin)) (syn_wo (.classEq B A) (.classMem (syn_copk A B) (syn_cltfin))) p0023
  have p0025 :=
    @g_lefinrflx A (syn_cnnc)
  have p0026 :=
    @g_adantr (.classMem A (syn_cnnc)) (.classMem (syn_copk A A) (syn_clefin)) (.classMem B (syn_cnnc)) p0025
  have p0027 :=
    @g_opkeq2 B A A
  have p0028 :=
    @g_eleq1d (.classEq B A) (syn_copk A B) (syn_copk A A) (syn_clefin) p0027
  have p0029 :=
    @g_syl5ibrcom (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin)) (.classEq B A) (.classMem (syn_copk A A) (syn_clefin)) p0026 p0028
  have p0030 :=
    @g_adantr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (.classEq B A) (.classMem (syn_copk A B) (syn_clefin))) (syn_wne B (syn_c0)) p0029
  have p0031 :=
    @g_ltlefin A B (syn_cnnc) (syn_cnnc)
  have p0032 :=
    @g_adantr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk A B) (syn_clefin))) (syn_wne B (syn_c0)) p0031
  have p0033 :=
    @g_jaod (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0))) (.classEq B A) (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk A B) (syn_cltfin)) p0030 p0032
  have p0034 :=
    @g_syld (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0))) (.neg (.classMem (syn_copk B A) (syn_cltfin))) (syn_wo (.classEq B A) (.classMem (syn_copk A B) (syn_cltfin))) (.classMem (syn_copk A B) (syn_clefin)) p0024 p0033
  have p0035 :=
    @g_expcom (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0)) (.imp (.neg (.classMem (syn_copk B A) (syn_cltfin))) (.classMem (syn_copk A B) (syn_clefin))) p0034
  have p0036 :=
    @g_pm2_61ine (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (.neg (.classMem (syn_copk B A) (syn_cltfin))) (.classMem (syn_copk A B) (syn_clefin)))) B (syn_c0) p0016 p0035
  have p0037 :=
    @g_impbid (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin)) (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0007 p0036
  exact p0037



#print axioms g_lenltfin

end NFChoice.DirectNominalPrf.WPPReplay
