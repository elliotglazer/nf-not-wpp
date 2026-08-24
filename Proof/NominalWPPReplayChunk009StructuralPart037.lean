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
import NominalWPPReplayChunk009StructuralPart036


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

noncomputable def g_addcnul1
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cplc A (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (h)
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (h)
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
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have p0000 :=
    @g_eq0 a (syn_cplc A (syn_c0)) (by exact (show a ∉ ((syn_cplc A (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((A).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))
  have p0001 :=
    @g_rex0 (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))) c
  have p0002 :=
    @g_a1i (.neg (syn_wrex c (syn_c0) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))))) (.classMem (.cv b) A) p0001
  have p0003 :=
    @g_nrex (syn_wrex c (syn_c0) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv a) (syn_cun (.cv b) (.cv c))))) b A p0002
  have p0004 :=
    @g_eladdc (.cv a) A (syn_c0) b c (by exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a))))))) (by exact (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a))))))) (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A))) (by exact (show c ∉ (A).fv from (by exact fresh_c_not_A))) (by exact (show b ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show c ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (show b ≠ c from (by exact fresh_b_ne_c))
  have p0005 :=
    @g_mtbir (.classMem (.cv a) (syn_cplc A (syn_c0))) (syn_wrex b A (syn_wrex c (syn_c0) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))))) p0003 p0004
  have p0006 :=
    @g_mpgbir (.classEq (syn_cplc A (syn_c0)) (syn_c0)) (.neg (.classMem (.cv a) (syn_cplc A (syn_c0)))) a p0000 p0005
  exact p0006

noncomputable def g_addcnnul
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wne (syn_cplc A B) (syn_c0)) (syn_wa (syn_wne A (syn_c0)) (syn_wne B (syn_c0)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_addceq1 A (syn_c0) B
  have p0001 :=
    @g_addccom (syn_c0) B
  have p0002 :=
    @g_addcnul1 B
  have p0003 :=
    @g_eqtri (syn_cplc (syn_c0) B) (syn_cplc B (syn_c0)) (syn_c0) p0001 p0002
  have p0004 :=
    @g_syl6eq (.classEq A (syn_c0)) (syn_cplc A B) (syn_cplc (syn_c0) B) (syn_c0) p0000 p0003
  have p0005 :=
    @g_necon3i A (syn_c0) (syn_cplc A B) (syn_c0) p0004
  have p0006 :=
    @g_addceq2 B (syn_c0) A
  have p0007 :=
    @g_addcnul1 A
  have p0008 :=
    @g_syl6eq (.classEq B (syn_c0)) (syn_cplc A B) (syn_cplc A (syn_c0)) (syn_c0) p0006 p0007
  have p0009 :=
    @g_necon3i B (syn_c0) (syn_cplc A B) (syn_c0) p0008
  have p0010 :=
    @g_jca (syn_wne (syn_cplc A B) (syn_c0)) (syn_wne A (syn_c0)) (syn_wne B (syn_c0)) p0005 p0009
  exact p0010



#print axioms g_addcnnul

end NFChoice.DirectNominalPrf.WPPReplay
