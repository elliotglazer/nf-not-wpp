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
import NominalWPPReplayChunk009StructuralPart024


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

noncomputable def g_nncex
     :
    Nominal.NPrf (.classMem (syn_cnnc) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_dfnnc2 x
  have p0001 :=
    @g_setswithex x (syn_c0c) (by exact (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0002 :=
    @g_ssetkex
  have p0003 :=
    @g_ssetkex
  have p0004 :=
    @g_addcexlem
  have p0005 :=
    @g_n_1cex
  have p0006 :=
    @g_pw1ex (syn_c1c) p0005
  have p0007 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0006
  have p0008 :=
    @g_imakex (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0004 p0007
  have p0009 :=
    @g_imagekex (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0008
  have p0010 :=
    @g_sikex (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0009
  have p0011 :=
    @g_cokex (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0003 p0010
  have p0012 :=
    @g_difex (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0002 p0011
  have p0013 :=
    @g_n_1cex
  have p0014 :=
    @g_imakex (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c) p0012 p0013
  have p0015 :=
    @g_difex (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)) p0001 p0014
  have p0016 :=
    @g_intex (syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c))) p0015
  have p0017 :=
    @g_eqeltri (syn_cnnc) (syn_cint (syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))) (syn_cvv) p0000 p0016
  exact p0017

noncomputable def g_finex
     :
    Nominal.NPrf (.classMem (syn_cfin) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cfin] using (Nominal.classEqRefl (syn_cfin)))
  have p0001 :=
    @g_nncex
  have p0002 :=
    @g_uniex (syn_cnnc) p0001
  have p0003 :=
    @g_eqeltri (syn_cfin) (syn_cuni (syn_cnnc)) (syn_cvv) p0000 p0002
  exact p0003

noncomputable def g_eladdc
    (A : Class) (M : Class) (N : Class) (b : Var) (c : Var) (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv) (dv_M_b : b ∉ M.fv) (dv_M_c : c ∉ M.fv) (dv_N_b : b ∉ N.fv) (dv_N_c : c ∉ N.fv) (dv_b_c : b ≠ c) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cplc M N)) (syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c))))))) := by
  let proofSupport : Finset Var := A.fv ∪ M.fv ∪ N.fv ∪ ({b} : Finset Var) ∪ ({c} : Finset Var)
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_ne_b : a ≠ b := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have p0000 :=
    @g_elex A (syn_cplc M N)
  have p0001 :=
    @g_id (.classEq A (syn_cun (.cv b) (.cv c)))
  have p0002 :=
    @g_vex b
  have p0003 :=
    @g_vex c
  have p0004 :=
    @g_unex (.cv b) (.cv c) p0002 p0003
  have p0005 :=
    @g_syl6eqel (.classEq A (syn_cun (.cv b) (.cv c))) A (syn_cun (.cv b) (.cv c)) (syn_cvv) p0001 p0004
  have p0006 :=
    @g_adantl (.classEq A (syn_cun (.cv b) (.cv c))) (.classMem A (syn_cvv)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0005
  have p0007 :=
    @g_rexlimivw (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c)))) (.classMem A (syn_cvv)) c N (by exact (show c ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ (A).fv from (by exact dv_A_c)) (show c ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0006
  have p0008 :=
    @g_rexlimivw (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c))))) (.classMem A (syn_cvv)) b M (by exact (show b ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (A).fv from (by exact dv_A_b)) (show b ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0007
  have p0009 :=
    @g_eqeq1 (.cv a) A (syn_cun (.cv b) (.cv c))
  have p0010 :=
    @g_anbi2d (.classEq (.cv a) A) (.classEq (.cv a) (syn_cun (.cv b) (.cv c))) (.classEq A (syn_cun (.cv b) (.cv c))) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0009
  have p0011 :=
    @g_n_2rexbidv (.classEq (.cv a) A) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c)))) b c M N (by exact (show b ∉ ((Wff.classEq (.cv a) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((Class.cv a)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ (A).fv from (by exact dv_A_b))))))) (by exact (show c ∉ ((Wff.classEq (.cv a) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show c ∉ (((Class.cv a)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ (A).fv from (by exact dv_A_c))))))) p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc a b c M N (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M))) (by exact (show b ∉ (M).fv from (by exact dv_M_b))) (by exact (show c ∉ (M).fv from (by exact dv_M_c))) (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) (by exact (show b ∉ (N).fv from (by exact dv_N_b))) (by exact (show c ∉ (N).fv from (by exact dv_N_c))) (show a ≠ b from (by exact fresh_a_ne_b)) (show a ≠ c from (by exact fresh_a_ne_c)) (show b ≠ c from (by exact dv_b_c))
  have p0013 :=
    @g_elab2g (syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))))) (syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c)))))) a A (syn_cplc M N) (syn_cvv) (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show a ∉ ((syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show a ∉ (((M).fv).erase b) ∪ ((((syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c)))))).fv).erase b) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((M).fv).erase b from (fun hmem => (show a ∉ (M).fv from (by exact fresh_a_not_M)) (Finset.mem_of_mem_erase hmem))) (show a ∉ (((syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c)))))).fv).erase b from (fun hmem => (show a ∉ ((syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show a ∉ (((N).fv).erase c) ∪ ((((syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c))))).fv).erase c) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((N).fv).erase c from (fun hmem => (show a ∉ (N).fv from (by exact fresh_a_not_N)) (Finset.mem_of_mem_erase hmem))) (show a ∉ (((syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c))))).fv).erase c from (fun hmem => (show a ∉ ((syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))).fv) ∪ (((Wff.classEq A (syn_cun (.cv b) (.cv c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_cin (.cv b) (.cv c))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cin (.cv b) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show a ∉ (((Class.cv b)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ b from (by exact fresh_a_ne_b)))))) (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))))))) (show a ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.classEq A (syn_cun (.cv b) (.cv c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ ((A).fv) ∪ (((syn_cun (.cv b) (.cv c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_cun (.cv b) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ (((Class.cv b)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ b from (by exact fresh_a_ne_b)))))) (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))))))))))))))) (Finset.mem_of_mem_erase hmem))))))) (Finset.mem_of_mem_erase hmem)))))))) p0011 p0012
  have p0014 :=
    @g_pm5_21nii (.classMem A (syn_cplc M N)) (.classMem A (syn_cvv)) (syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv c)))))) p0000 p0008 p0013
  exact p0014

noncomputable def g_eladdci
    (A : Class) (B : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A M) (.classMem B N) (.classEq (syn_cin A B) (syn_c0))) (.classMem (syn_cun A B) (syn_cplc M N))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have p0000 :=
    @g_eqid (syn_cun A B)
  have p0001 :=
    @g_ineq1 (.cv a) A (.cv b)
  have p0002 :=
    @g_eqeq1d (.classEq (.cv a) A) (syn_cin (.cv a) (.cv b)) (syn_cin A (.cv b)) (syn_c0) p0001
  have p0003 :=
    @g_uneq1 (.cv a) A (.cv b)
  have p0004 :=
    @g_eqeq2d (.classEq (.cv a) A) (syn_cun (.cv a) (.cv b)) (syn_cun A (.cv b)) (syn_cun A B) p0003
  have p0005 :=
    @g_anbi12d (.classEq (.cv a) A) (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin A (.cv b)) (syn_c0)) (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b))) (.classEq (syn_cun A B) (syn_cun A (.cv b))) p0002 p0004
  have p0006 :=
    @g_ineq2 (.cv b) B A
  have p0007 :=
    @g_eqeq1d (.classEq (.cv b) B) (syn_cin A (.cv b)) (syn_cin A B) (syn_c0) p0006
  have p0008 :=
    @g_uneq2 (.cv b) B A
  have p0009 :=
    @g_eqeq2d (.classEq (.cv b) B) (syn_cun A (.cv b)) (syn_cun A B) (syn_cun A B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv b) B) (.classEq (syn_cin A (.cv b)) (syn_c0)) (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A (.cv b))) (.classEq (syn_cun A B) (syn_cun A B)) p0007 p0009
  have p0011 :=
    @g_rspc2ev (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A B))) (syn_wa (.classEq (syn_cin A (.cv b)) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A (.cv b)))) a b A B M N (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A))) (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B))) (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M))) (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N))) (by exact (show a ∉ ((syn_wa (.classEq (syn_cin A (.cv b)) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A (.cv b))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.classEq (syn_cin A (.cv b)) (syn_c0))).fv) ∪ (((Wff.classEq (syn_cun A B) (syn_cun A (.cv b)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classEq (syn_cin A (.cv b)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_cin A (.cv b))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cin A (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show a ∉ ((A).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ b from (by exact fresh_a_ne_b)))))))))) (show a ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.classEq (syn_cun A B) (syn_cun A (.cv b)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_cun A B)).fv) ∪ (((syn_cun A (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ (B).fv from (by exact fresh_a_not_B)))))) (show a ∉ ((syn_cun A (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ ((A).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ b from (by exact fresh_a_ne_b))))))))))))))))))) (by exact (show b ∉ ((syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A B)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classEq (syn_cin A B) (syn_c0))).fv) ∪ (((Wff.classEq (syn_cun A B) (syn_cun A B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((syn_cin A B)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cin A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show b ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (A).fv from (by exact fresh_b_not_A)) (show b ∉ (B).fv from (by exact fresh_b_not_B)))))) (show b ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classEq (syn_cun A B) (syn_cun A B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((syn_cun A B)).fv) ∪ (((syn_cun A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show b ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (A).fv from (by exact fresh_b_not_A)) (show b ∉ (B).fv from (by exact fresh_b_not_B)))))) (show b ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show b ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (A).fv from (by exact fresh_b_not_A)) (show b ∉ (B).fv from (by exact fresh_b_not_B))))))))))))))) (show a ≠ b from (by exact fresh_a_ne_b)) p0005 p0010
  have p0012 :=
    @g_n_3expa (.classMem A M) (.classMem B N) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A B))) (syn_wrex a M (syn_wrex b N (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b)))))) p0011
  have p0013 :=
    @g_mpanr2 (syn_wa (.classMem A M) (.classMem B N)) (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A B)) (syn_wrex a M (syn_wrex b N (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b)))))) p0000 p0012
  have p0014 :=
    @g_n_3impa (.classMem A M) (.classMem B N) (.classEq (syn_cin A B) (syn_c0)) (syn_wrex a M (syn_wrex b N (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b)))))) p0013
  have p0015 :=
    @g_eladdc (syn_cun A B) M N a b (by exact (show a ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ (B).fv from (by exact fresh_a_not_B))))))) (by exact (show b ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show b ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (A).fv from (by exact fresh_b_not_A)) (show b ∉ (B).fv from (by exact fresh_b_not_B))))))) (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M))) (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N))) (show a ≠ b from (by exact fresh_a_ne_b))
  have p0016 :=
    @g_sylibr (syn_w3a (.classMem A M) (.classMem B N) (.classEq (syn_cin A B) (syn_c0))) (syn_wrex a M (syn_wrex b N (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b)))))) (.classMem (syn_cun A B) (syn_cplc M N)) p0014 p0015
  exact p0016

noncomputable def g_n_0nelsuc
    (A : Class) :
    Nominal.NPrf (.neg (.classMem (syn_c0) (syn_cplc A (syn_c1c)))) := by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have p0000 :=
    @g_el1c n (.cv m) (by exact (show n ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ m from (by exact fresh_n_ne_m)))))))
  have p0001 :=
    @g_vex n
  have p0002 :=
    @g_snid (.cv n) p0001
  have p0003 :=
    @g_n0i (syn_csn (.cv n)) (.cv n)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_eqeq1 (.cv m) (syn_csn (.cv n)) (syn_c0)
  have p0006 :=
    @g_mtbiri (.classEq (.cv m) (syn_csn (.cv n))) (.classEq (.cv m) (syn_c0)) (.classEq (syn_csn (.cv n)) (syn_c0)) p0004 p0005
  have p0007 :=
    @g_exlimiv (.classEq (.cv m) (syn_csn (.cv n))) (.neg (.classEq (.cv m) (syn_c0))) n (by exact (show n ∉ ((Wff.neg (.classEq (.cv m) (syn_c0)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show n ∉ ((Wff.classEq (.cv m) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((Class.cv m)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ m from (by exact fresh_n_ne_m)))))) (show n ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) p0006
  have p0008 :=
    @g_sylbi (.classMem (.cv m) (syn_c1c)) (syn_wex n (.classEq (.cv m) (syn_csn (.cv n)))) (.neg (.classEq (.cv m) (syn_c0))) p0000 p0007
  have p0009 :=
    @g_simpr (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0))
  have p0010 :=
    @g_nsyl (.classMem (.cv m) (syn_c1c)) (.classEq (.cv m) (syn_c0)) (syn_wa (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0))) p0008 p0009
  have p0011 :=
    @g_un00 (.cv n) (.cv m)
  have p0012 :=
    @g_eqcom (syn_cun (.cv n) (.cv m)) (syn_c0)
  have p0013 :=
    @g_bitri (syn_wa (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0))) (.classEq (syn_cun (.cv n) (.cv m)) (syn_c0)) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))) p0011 p0012
  have p0014 :=
    @g_notbii (syn_wa (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0))) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))) p0013
  have p0015 :=
    @g_sylib (.classMem (.cv m) (syn_c1c)) (.neg (syn_wa (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0)))) (.neg (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))) p0010 p0014
  have p0016 :=
    @g_simpr (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0)) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))
  have p0017 :=
    @g_nsyl (.classMem (.cv m) (syn_c1c)) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))) (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0)) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))) p0015 p0016
  have p0018 :=
    @g_nrex (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0)) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))) m (syn_c1c) p0017
  have p0019 :=
    @g_a1i (.neg (syn_wrex m (syn_c1c) (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0)) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))))) (.classMem (.cv n) A) p0018
  have p0020 :=
    @g_nrex (syn_wrex m (syn_c1c) (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0)) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))))) n A p0019
  have p0021 :=
    @g_eladdc (syn_c0) A (syn_c1c) n m (by exact (show n ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A))) (by exact (show m ∉ (A).fv from (by exact fresh_m_not_A))) (by exact (show n ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (show n ≠ m from (by exact fresh_n_ne_m))
  have p0022 :=
    @g_mtbir (.classMem (syn_c0) (syn_cplc A (syn_c1c))) (syn_wrex n A (syn_wrex m (syn_c1c) (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0)) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))))) p0020 p0021
  exact p0022

noncomputable def g_n_0cnsuc
    (A : Class) :
    Nominal.NPrf (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_n_0nelsuc A
  have p0001 :=
    @g_n_0ex
  have p0002 :=
    @g_snid (syn_c0) p0001
  have p0003 :=
    (by simpa [syn_c0c] using (Nominal.classEqRefl (syn_c0c)))
  have p0004 :=
    @g_eleqtrri (syn_c0) (syn_csn (syn_c0)) (syn_c0c) p0002 p0003
  have p0005 :=
    @g_eleq2 (syn_cplc A (syn_c1c)) (syn_c0c) (syn_c0)
  have p0006 :=
    @g_mpbiri (.classEq (syn_cplc A (syn_c1c)) (syn_c0c)) (.classMem (syn_c0) (syn_cplc A (syn_c1c))) (.classMem (syn_c0) (syn_c0c)) p0004 p0005
  have p0007 :=
    @g_mto (.classEq (syn_cplc A (syn_c1c)) (syn_c0c)) (.classMem (syn_c0) (syn_cplc A (syn_c1c))) p0000 p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c))))
  have p0009 :=
    @g_mpbir (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c)) (.neg (.classEq (syn_cplc A (syn_c1c)) (syn_c0c))) p0007 p0008
  exact p0009

noncomputable def g_peano1
     :
    Nominal.NPrf (.classMem (syn_c0c) (syn_cnnc)) := by
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nnc y x (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 :=
    @g_eleq2i (syn_cnnc) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))))) (syn_c0c) p0000
  have p0002 :=
    @g_n_0cex
  have p0003 :=
    @g_elintab (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) x (syn_c0c) (by exact (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) p0002
  have p0004 :=
    @g_bitri (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0c) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))))) (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.classMem (syn_c0c) (.cv x)))) p0001 p0003
  have p0005 :=
    @g_simpl (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))
  have p0006 :=
    @g_mpgbir (.classMem (syn_c0c) (syn_cnnc)) (.imp (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.classMem (syn_c0c) (.cv x))) x p0004 p0005
  exact p0006

noncomputable def g_peano2
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))) := by
  let proofSupport : Finset Var := A.fv
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_addceq1 (.cv a) A (syn_c1c)
  have p0001 :=
    @g_eleq1d (.classEq (.cv a) A) (syn_cplc (.cv a) (syn_c1c)) (syn_cplc A (syn_c1c)) (syn_cnnc) p0000
  have p0002 :=
    @g_addceq1 (.cv y) (.cv a) (syn_c1c)
  have p0003_e00_recanon : Nominal.NPrf (.imp (.objEq y a) (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv a) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0002
  have p0003 :=
    @g_eleq1d (.objEq y a) (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv a) (syn_c1c)) (.cv x) p0003_e00_recanon
  have p0004_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (.cv a)) (syn_wb (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0004 :=
    @g_rspccv (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)) y (.cv a) (.cv x) (by exact (show y ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ a from (by exact fresh_y_ne_a))))))) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ ((Wff.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_cplc (.cv a) (syn_c1c))).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cplc (.cv a) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((Class.cv a)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ a from (by exact fresh_y_ne_a)))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))) p0004_e00_recanon
  have p0005_e00_recanon : Nominal.NPrf (.imp (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))) (.imp (.objMem a x) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wral syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0005 :=
    @g_adantl (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))) (.imp (.objMem a x) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x))) (.classMem (syn_c0c) (.cv x)) p0005_e00_recanon
  have p0006 :=
    @g_a2i (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.objMem a x) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)) p0005
  have p0007 :=
    @g_alimi (.imp (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.objMem a x)) (.imp (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x))) x p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nnc y x (show x ≠ y from (by exact fresh_x_ne_y))
  have p0009 :=
    @g_eleq2i (syn_cnnc) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))))) (.cv a) p0008
  have p0010 :=
    @g_vex a
  have p0011 :=
    @g_elintab (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) x (.cv a) (by exact (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a))))))) p0010
  have p0012_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv a) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))))) (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.objMem a x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_wral syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0011
  have p0012 :=
    @g_bitri (.classMem (.cv a) (syn_cnnc)) (.classMem (.cv a) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))))) (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.objMem a x))) p0009 p0012_e01_recanon
  have p0013 :=
    @g_eleq2i (syn_cnnc) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))))) (syn_cplc (.cv a) (syn_c1c)) p0008
  have p0014 :=
    @g_n_1cex
  have p0015 :=
    @g_addcex (.cv a) (syn_c1c) p0010 p0014
  have p0016 :=
    @g_elintab (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) x (syn_cplc (.cv a) (syn_c1c)) (by exact (show x ∉ ((syn_cplc (.cv a) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv a)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0015
  have p0017 :=
    @g_bitri (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))))) (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)))) p0013 p0016
  have p0018 :=
    @g_n_3imtr4i (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.objMem a x))) (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x)) (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)))) (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc)) p0007 p0012 p0017
  have p0019 :=
    @g_vtoclga (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) a A (syn_cnnc) (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show a ∉ ((Wff.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((syn_cplc A (syn_c1c))).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cplc A (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((A).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0001 p0018
  exact p0019

noncomputable def g_peano3
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_n_0cnsuc A
  have p0001 :=
    @g_a1i (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c)) (.classMem A (syn_cnnc)) p0000
  exact p0001

noncomputable def g_addcid1
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cplc A (syn_c0c)) A) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have p0000 :=
    (by simpa [syn_c0c] using (Nominal.classEqRefl (syn_c0c)))
  have p0001 :=
    @g_addceq2i (syn_c0c) (syn_csn (syn_c0)) A p0000
  have p0002 :=
    @g_n_0ex
  have p0003 :=
    @g_ineq2 (.cv z) (syn_c0) (.cv y)
  have p0004 :=
    @g_eqeq1d (.classEq (.cv z) (syn_c0)) (syn_cin (.cv y) (.cv z)) (syn_cin (.cv y) (syn_c0)) (syn_c0) p0003
  have p0005 :=
    @g_uneq2 (.cv z) (syn_c0) (.cv y)
  have p0006 :=
    @g_eqeq2d (.classEq (.cv z) (syn_c0)) (syn_cun (.cv y) (.cv z)) (syn_cun (.cv y) (syn_c0)) (.cv x) p0005
  have p0007 :=
    @g_anbi12d (.classEq (.cv z) (syn_c0)) (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (syn_cin (.cv y) (syn_c0)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z))) (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) p0004 p0006
  have p0008 :=
    @g_in0 (.cv y)
  have p0009 :=
    @g_biantrur (.classEq (syn_cin (.cv y) (syn_c0)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) p0008
  have p0010 :=
    @g_syl6bbr (.classEq (.cv z) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))) (syn_wa (.classEq (syn_cin (.cv y) (syn_c0)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (syn_c0)))) (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) p0007 p0009
  have p0011 :=
    @g_rexsn (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))) (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) z (syn_c0) (by exact (show z ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show z ∉ ((Wff.classEq (.cv x) (syn_cun (.cv y) (syn_c0)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((syn_cun (.cv y) (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((syn_cun (.cv y) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show z ∉ (((Class.cv y)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))) (show z ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0002 p0010
  have p0012 :=
    @g_un0 (.cv y)
  have p0013 :=
    @g_eqeq2i (syn_cun (.cv y) (syn_c0)) (.cv y) (.cv x) p0012
  have p0014 :=
    @g_equcom x y
  have p0015_e01_recanon : Nominal.NPrf (syn_wb (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_c0 syn_cdif syn_cin syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0013
  have p0015 :=
    @g_n_3bitri (syn_wrex z (syn_csn (syn_c0)) (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))) (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) (.objEq x y) (.objEq y x) p0011 p0015_e01_recanon p0014
  have p0016 :=
    @g_rexbii (syn_wrex z (syn_csn (syn_c0)) (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))) (.objEq y x) y A p0015
  have p0017 :=
    @g_eladdc (.cv x) A (syn_csn (syn_c0)) y z (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show y ∉ ((syn_csn (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))) (by exact (show z ∉ ((syn_csn (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0018 :=
    @g_risset y (.cv x) A (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0019_e02_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) A) (syn_wrex y A (.objEq y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0018
  have p0019 :=
    @g_n_3bitr4i (syn_wrex y A (syn_wrex z (syn_csn (syn_c0)) (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))) (syn_wrex y A (.objEq y x)) (.classMem (.cv x) (syn_cplc A (syn_csn (syn_c0)))) (.classMem (.cv x) A) p0016 p0017 p0019_e02_recanon
  have p0020 :=
    @g_eqriv x (syn_cplc A (syn_csn (syn_c0))) A (by exact (show x ∉ ((syn_cplc A (syn_csn (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((syn_csn (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_csn (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) p0019
  have p0021 :=
    @g_eqtri (syn_cplc A (syn_c0c)) (syn_cplc A (syn_csn (syn_c0))) A p0001 p0020
  exact p0021



#print axioms g_addcid1

end NFChoice.DirectNominalPrf.WPPReplay
