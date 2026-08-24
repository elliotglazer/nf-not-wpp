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
import NominalWPPReplayChunk009StructuralPart029


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

noncomputable def g_addc32
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cplc (syn_cplc A B) C) (syn_cplc (syn_cplc A C) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_addccom B C
  have p0001 :=
    @g_addceq2i (syn_cplc B C) (syn_cplc C B) A p0000
  have p0002 :=
    @g_addcass A B C
  have p0003 :=
    @g_addcass A C B
  have p0004 :=
    @g_n_3eqtr4i (syn_cplc A (syn_cplc B C)) (syn_cplc A (syn_cplc C B)) (syn_cplc (syn_cplc A B) C) (syn_cplc (syn_cplc A C) B) p0001 p0002 p0003
  exact p0004

noncomputable def g_addc4
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.classEq (syn_cplc (syn_cplc A B) (syn_cplc C D)) (syn_cplc (syn_cplc A C) (syn_cplc B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_addc32 A B C
  have p0001 :=
    @g_addceq1i (syn_cplc (syn_cplc A B) C) (syn_cplc (syn_cplc A C) B) D p0000
  have p0002 :=
    @g_addcass (syn_cplc A B) C D
  have p0003 :=
    @g_addcass (syn_cplc A C) B D
  have p0004 :=
    @g_n_3eqtr3i (syn_cplc (syn_cplc (syn_cplc A B) C) D) (syn_cplc (syn_cplc (syn_cplc A C) B) D) (syn_cplc (syn_cplc A B) (syn_cplc C D)) (syn_cplc (syn_cplc A C) (syn_cplc B D)) p0001 p0002 p0003
  exact p0004

noncomputable def g_addc6
    (A : Class) (B : Class) (C : Class) (D : Class) (E : Class) (F : Class) :
    Nominal.NPrf (.classEq (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) (syn_cplc E F)) (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc (syn_cplc B D) F))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ E.fv ∪ F.fv
  have p0000 :=
    @g_addc4 A B C D
  have p0001 :=
    @g_addceq1i (syn_cplc (syn_cplc A B) (syn_cplc C D)) (syn_cplc (syn_cplc A C) (syn_cplc B D)) E p0000
  have p0002 :=
    @g_addc32 (syn_cplc A C) (syn_cplc B D) E
  have p0003 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) E) (syn_cplc (syn_cplc (syn_cplc A C) (syn_cplc B D)) E) (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc B D)) p0001 p0002
  have p0004 :=
    @g_addceq1i (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) E) (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc B D)) F p0003
  have p0005 :=
    @g_addcass (syn_cplc (syn_cplc A B) (syn_cplc C D)) E F
  have p0006 :=
    @g_addcass (syn_cplc (syn_cplc A C) E) (syn_cplc B D) F
  have p0007 :=
    @g_n_3eqtr3i (syn_cplc (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) E) F) (syn_cplc (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc B D)) F) (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) (syn_cplc E F)) (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc (syn_cplc B D) F)) p0004 p0005 p0006
  exact p0007

noncomputable def g_nncaddccl
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_cplc A B) (syn_cnnc))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (h))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_c_ne_x : c ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have p0000 :=
    @g_addceq1 (.cv a) A B
  have p0001 :=
    @g_eleq1d (.classEq (.cv a) A) (syn_cplc (.cv a) B) (syn_cplc A B) (syn_cnnc) p0000
  have p0002 :=
    @g_imbi2d (.classEq (.cv a) A) (.classMem (syn_cplc (.cv a) B) (syn_cnnc)) (.classMem (syn_cplc A B) (syn_cnnc)) (.classMem B (syn_cnnc)) p0001
  have p0003 :=
    @g_unab (.neg (.classMem (.cv a) (syn_cnnc))) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) b
  have p0004 :=
    @g_vex b
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_opkelimagekg (.cv b) (.cv x) (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))) (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_mp2an (.classMem (.cv b) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv b) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (.classEq (.cv x) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))) (.cv b)))) p0004 p0005 p0006
  have p0008 :=
    @g_opkelcnvk (.cv x) (.cv b) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))))) p0005 p0004
  have p0009 :=
    @g_addccom (.cv a) (.cv b)
  have p0010 :=
    @g_dfaddc2 (.cv b) (.cv a)
  have p0011 :=
    @g_eqtri (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv b) (.cv a)) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))) (.cv b)) p0009 p0010
  have p0012 :=
    @g_eqeq2i (syn_cplc (.cv a) (.cv b)) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))) (.cv b)) (.cv x) p0011
  have p0013 :=
    @g_n_3bitr4i (.classMem (syn_copk (.cv b) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (.classEq (.cv x) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))) (.cv b))) (.classMem (syn_copk (.cv x) (.cv b)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))))))) (.classEq (.cv x) (syn_cplc (.cv a) (.cv b))) p0007 p0008 p0012
  have p0014 :=
    @g_rexbii (.classMem (syn_copk (.cv x) (.cv b)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))))))) (.classEq (.cv x) (syn_cplc (.cv a) (.cv b))) x (syn_cnnc) p0013
  have p0015 :=
    @g_elimak x (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc) (.cv b) (by exact (show x ∉ ((syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show x ∉ ((syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek]; exact (show x ∉ ((syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show x ∉ (((syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) ∪ (((syn_cpw1 (syn_cpw1 (.cv a)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show x ∉ (((syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv) ∪ (((syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ ((syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ ((syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show x ∉ (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show x ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))) (show x ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show x ∉ ((syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show x ∉ (((syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show x ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ (((syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show x ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪ (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show x ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show x ∉ ((syn_csik (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))) (show x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))))) (show x ∉ ((syn_cpw1 (syn_cpw1 (.cv a)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a))))))))))))))))))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ b from (by exact fresh_x_ne_b))))))) p0004
  have p0016 :=
    @g_risset x (syn_cplc (.cv a) (.cv b)) (syn_cnnc) (by exact (show x ∉ ((syn_cplc (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a)))))) (show x ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ b from (by exact fresh_x_ne_b))))))))))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0017 :=
    @g_n_3bitr4i (syn_wrex x (syn_cnnc) (.classMem (syn_copk (.cv x) (.cv b)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))))) (syn_wrex x (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv a) (.cv b)))) (.classMem (.cv b) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc))) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) p0014 p0015 p0016
  have p0018 :=
    @g_eqabi (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) b (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc)) (by exact (show b ∉ ((syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show b ∉ (((syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))))))).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show b ∉ ((syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek]; exact (show b ∉ ((syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show b ∉ (((syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) ∪ (((syn_cpw1 (syn_cpw1 (.cv a)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show b ∉ (((syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv) ∪ (((syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show b ∉ ((syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show b ∉ ((syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show b ∉ (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show b ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show b ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show b ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show b ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))) (show b ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show b ∉ ((syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show b ∉ (((syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show b ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ (((syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show b ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show b ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show b ∉ (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪ (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show b ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show b ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show b ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show b ∉ ((syn_csik (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show b ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))) (show b ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))))) (show b ∉ ((syn_cpw1 (syn_cpw1 (.cv a)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))))))))))))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0017
  have p0019 :=
    @g_uneq2i (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc)) (.cab b (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))) (.cab b (.neg (.classMem (.cv a) (syn_cnnc)))) p0018
  have p0020 :=
    @g_imor (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))
  have p0021 :=
    @g_abbii (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))) (syn_wo (.neg (.classMem (.cv a) (syn_cnnc))) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))) b p0020
  have p0022 :=
    @g_n_3eqtr4i (syn_cun (.cab b (.neg (.classMem (.cv a) (syn_cnnc)))) (.cab b (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))) (.cab b (syn_wo (.neg (.classMem (.cv a) (syn_cnnc))) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))) (syn_cun (.cab b (.neg (.classMem (.cv a) (syn_cnnc)))) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc))) (.cab b (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))) p0003 p0019 p0021
  have p0023 :=
    @g_abexv (.neg (.classMem (.cv a) (syn_cnnc))) b (by exact (show b ∉ ((Wff.neg (.classMem (.cv a) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show b ∉ ((Wff.classMem (.cv a) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))
  have p0024 :=
    @g_addcexlem
  have p0025 :=
    @g_vex a
  have p0026 :=
    @g_pw1ex (.cv a) p0025
  have p0027 :=
    @g_pw1ex (syn_cpw1 (.cv a)) p0026
  have p0028 :=
    @g_imakex (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))) p0024 p0027
  have p0029 :=
    @g_imagekex (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))) p0028
  have p0030 :=
    @g_cnvkex (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a))))) p0029
  have p0031 :=
    @g_nncex
  have p0032 :=
    @g_imakex (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc) p0030 p0031
  have p0033 :=
    @g_unex (.cab b (.neg (.classMem (.cv a) (syn_cnnc)))) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc)) p0023 p0032
  have p0034 :=
    @g_eqeltrri (syn_cun (.cab b (.neg (.classMem (.cv a) (syn_cnnc)))) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc))) (.cab b (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))) (syn_cvv) p0022 p0033
  have p0035 :=
    @g_addceq2 (.cv b) (syn_c0c) (.cv a)
  have p0036 :=
    @g_eleq1d (.classEq (.cv b) (syn_c0c)) (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc) p0035
  have p0037 :=
    @g_imbi2d (.classEq (.cv b) (syn_c0c)) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc)) (.classMem (.cv a) (syn_cnnc)) p0036
  have p0038 :=
    @g_addceq2 (.cv b) (.cv c) (.cv a)
  have p0039_e00_recanon : Nominal.NPrf (.imp (.objEq b c) (.classEq (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv a) (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0038
  have p0039 :=
    @g_eleq1d (.objEq b c) (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv a) (.cv c)) (syn_cnnc) p0039_e00_recanon
  have p0040 :=
    @g_imbi2d (.objEq b c) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc)) (.classMem (.cv a) (syn_cnnc)) p0039
  have p0041 :=
    @g_addceq2 (.cv b) (syn_cplc (.cv c) (syn_c1c)) (.cv a)
  have p0042 :=
    @g_eleq1d (.classEq (.cv b) (syn_cplc (.cv c) (syn_c1c))) (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc) p0041
  have p0043 :=
    @g_imbi2d (.classEq (.cv b) (syn_cplc (.cv c) (syn_c1c))) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc)) (.classMem (.cv a) (syn_cnnc)) p0042
  have p0044 :=
    @g_addceq2 (.cv b) B (.cv a)
  have p0045 :=
    @g_eleq1d (.classEq (.cv b) B) (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv a) B) (syn_cnnc) p0044
  have p0046 :=
    @g_imbi2d (.classEq (.cv b) B) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) (.classMem (syn_cplc (.cv a) B) (syn_cnnc)) (.classMem (.cv a) (syn_cnnc)) p0045
  have p0047 :=
    @g_addcid1 (.cv a)
  have p0048 :=
    @g_id (.classMem (.cv a) (syn_cnnc))
  have p0049 :=
    @g_syl5eqel (.classMem (.cv a) (syn_cnnc)) (syn_cplc (.cv a) (syn_c0c)) (.cv a) (syn_cnnc) p0047 p0048
  have p0050 :=
    @g_addcass (.cv a) (.cv c) (syn_c1c)
  have p0051 :=
    @g_peano2 (syn_cplc (.cv a) (.cv c))
  have p0052 :=
    @g_syl5eqelr (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc)) (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cplc (syn_cplc (.cv a) (.cv c)) (syn_c1c)) (syn_cnnc) p0050 p0051
  have p0053 :=
    @g_imim2i (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc)) (.classMem (.cv a) (syn_cnnc)) p0052
  have p0054 :=
    @g_a1i (.imp (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc))) (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc)))) (.classMem (.cv c) (syn_cnnc)) p0053
  have p0055 :=
    @g_finds (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))) (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc))) (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc))) (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc))) (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) B) (syn_cnnc))) b c B (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B))) (by exact (show b ∉ ((Wff.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((Wff.classMem (.cv a) (syn_cnnc))).fv) ∪ (((Wff.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem (.cv a) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cplc (.cv a) (.cv c))).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cplc (.cv a) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c)))))))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show c ∉ ((Wff.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show c ∉ (((Wff.classMem (.cv a) (syn_cnnc))).fv) ∪ (((Wff.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Wff.classMem (.cv a) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show c ∉ ((Wff.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((syn_cplc (.cv a) (.cv b))).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_cplc (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ b from (by exact fresh_c_ne_b)))))))))) (show c ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show b ∉ ((Wff.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((Wff.classMem (.cv a) (syn_cnnc))).fv) ∪ (((Wff.classMem (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem (.cv a) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classMem (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cplc (.cv a) (syn_c0c))).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cplc (.cv a) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show b ∉ ((Wff.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) B) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((Wff.classMem (.cv a) (syn_cnnc))).fv) ∪ (((Wff.classMem (syn_cplc (.cv a) B) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem (.cv a) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classMem (syn_cplc (.cv a) B) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cplc (.cv a) B)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cplc (.cv a) B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv a)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ (B).fv from (by exact fresh_b_not_B)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show b ∉ ((Wff.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((Wff.classMem (.cv a) (syn_cnnc))).fv) ∪ (((Wff.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem (.cv a) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c)))).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_cplc (.cv c) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_cplc (.cv c) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv c)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c)))))) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show b ≠ c from (by exact fresh_b_ne_c)) p0034 p0037 p0040 p0043 p0046 p0049 p0054
  have p0056 :=
    @g_com12 (.classMem B (syn_cnnc)) (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) B) (syn_cnnc)) p0055
  have p0057 :=
    @g_vtoclga (.imp (.classMem B (syn_cnnc)) (.classMem (syn_cplc (.cv a) B) (syn_cnnc))) (.imp (.classMem B (syn_cnnc)) (.classMem (syn_cplc A B) (syn_cnnc))) a A (syn_cnnc) (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show a ∉ ((Wff.imp (.classMem B (syn_cnnc)) (.classMem (syn_cplc A B) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show a ∉ (((Wff.classMem B (syn_cnnc))).fv) ∪ (((Wff.classMem (syn_cplc A B) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classMem B (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((B).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (B).fv from (by exact fresh_a_not_B)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.classMem (syn_cplc A B) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((syn_cplc A B)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cplc A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ (B).fv from (by exact fresh_a_not_B)))))) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0002 p0056
  have p0058 :=
    @g_imp (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem (syn_cplc A B) (syn_cnnc)) p0057
  exact p0058

noncomputable def g_elfin
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cfin)) (syn_wrex x (syn_cnnc) (.classMem A (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    (by simpa [syn_cfin] using (Nominal.classEqRefl (syn_cfin)))
  have p0001 :=
    @g_eleq2i (syn_cfin) (syn_cuni (syn_cnnc)) A p0000
  have p0002 :=
    @g_eluni2 x A (syn_cnnc) (by exact (show x ∉ (A).fv from (by exact dv_A_x))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0003 :=
    @g_bitri (.classMem A (syn_cfin)) (.classMem A (syn_cuni (syn_cnnc))) (syn_wrex x (syn_cnnc) (.classMem A (.cv x))) p0001 p0002
  exact p0003

noncomputable def g_el0c
    (A : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_c0c)) (.classEq A (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_c0c] using (Nominal.classEqRefl (syn_c0c)))
  have p0001 :=
    @g_eleq2i (syn_c0c) (syn_csn (syn_c0)) A p0000
  have p0002 :=
    @g_n_0ex
  have p0003 :=
    @g_elsnc2 A (syn_c0) p0002
  have p0004 :=
    @g_bitri (.classMem A (syn_c0c)) (.classMem A (syn_csn (syn_c0))) (.classEq A (syn_c0)) p0001 p0003
  exact p0004

noncomputable def g_nulel0c
     :
    Nominal.NPrf (.classMem (syn_c0) (syn_c0c)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_eqid (syn_c0)
  have p0001 :=
    @g_el0c (syn_c0)
  have p0002 :=
    @g_mpbir (.classMem (syn_c0) (syn_c0c)) (.classEq (syn_c0) (syn_c0)) p0000 p0001
  exact p0002



#print axioms g_nulel0c

end NFChoice.DirectNominalPrf.WPPReplay
