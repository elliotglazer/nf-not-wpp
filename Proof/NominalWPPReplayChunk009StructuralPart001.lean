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
import NominalWPPReplayChunk008


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

noncomputable def g_elpw1101c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))))))))
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw191c x (.cv y) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y))) x (by exact (show x ∉ ((Wff.classEq A (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))))))
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) y (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))) (by exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))))))))))))))))))) (by exact (show y ∉ ((Wff.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))))))))))))))))))))))))) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))) p0000 p0015
  exact p0016

noncomputable def g_elpw1111c
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elpw1 y A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))))))))))
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (.classEq A (syn_csn (.cv y))))))
  have p0002 :=
    @g_elpw1101c x (.cv y) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))
  have p0003 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))) (.classEq A (syn_csn (.cv y))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y))) x (by exact (show x ∉ ((Wff.classEq A (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))))))
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y))))) y p0005
  have p0007 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (.classEq A (syn_csn (.cv y))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y)))))) p0001 p0006
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y)))) y x
  have p0009 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
  have p0010 :=
    @g_sneq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (syn_csn (.cv y)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) A p0010
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))) y (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))) (by exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))))))))))))))))))))) (by exact (show y ∉ ((Wff.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))))))))))))))))))))))))))) p0009 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y))))) (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))) x p0012
  have p0014 :=
    @g_bitri (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))) p0008 p0013
  have p0015 :=
    @g_bitri (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))) (.classEq A (syn_csn (.cv y)))))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))) p0007 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (.classEq A (syn_csn (.cv y)))) (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))) p0000 p0015
  exact p0016

noncomputable def g_pw1ss1c
    (A : Class) :
    Nominal.NPrf (syn_wss (syn_cpw1 A) (syn_c1c)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cpw1] using (Nominal.classEqRefl (syn_cpw1 A)))
  have p0001 :=
    @g_inss2 (syn_cpw A) (syn_c1c)
  have p0002 :=
    @g_eqsstri (syn_cpw1 A) (syn_cin (syn_cpw A) (syn_c1c)) (syn_c1c) p0000 p0001
  exact p0002

noncomputable def g_n_0nel1c
     :
    Nominal.NPrf (.neg (.classMem (syn_c0) (syn_c1c))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_snprc (.cv x)
  have p0002 :=
    @g_eqcom (syn_csn (.cv x)) (syn_c0)
  have p0003 :=
    @g_bitri (.neg (.classMem (.cv x) (syn_cvv))) (.classEq (syn_csn (.cv x)) (syn_c0)) (.classEq (syn_c0) (syn_csn (.cv x))) p0001 p0002
  have p0004 :=
    @g_con1bii (.classMem (.cv x) (syn_cvv)) (.classEq (syn_c0) (syn_csn (.cv x))) p0003
  have p0005 :=
    @g_mpbir (.neg (.classEq (syn_c0) (syn_csn (.cv x)))) (.classMem (.cv x) (syn_cvv)) p0000 p0004
  have p0006 :=
    @g_nex (.classEq (syn_c0) (syn_csn (.cv x))) x p0005
  have p0007 :=
    @g_el1c x (syn_c0) (by exact (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0008 :=
    @g_mtbir (.classMem (syn_c0) (syn_c1c)) (syn_wex x (.classEq (syn_c0) (syn_csn (.cv x)))) p0006 p0007
  exact p0008

noncomputable def g_pw0
     :
    Nominal.NPrf (.classEq (syn_cpw (syn_c0)) (syn_csn (syn_c0))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_ss0b (.cv x)
  have p0001 :=
    @g_abbii (syn_wss (.cv x) (syn_c0)) (.classEq (.cv x) (syn_c0)) x p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x (syn_c0) (by exact (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x (syn_c0) (by exact (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0004 :=
    @g_n_3eqtr4i (.cab x (syn_wss (.cv x) (syn_c0))) (.cab x (.classEq (.cv x) (syn_c0))) (syn_cpw (syn_c0)) (syn_csn (syn_c0)) p0001 p0002 p0003
  exact p0004

noncomputable def g_pw10
     :
    Nominal.NPrf (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    (by simpa [syn_cpw1] using (Nominal.classEqRefl (syn_cpw1 (syn_c0))))
  have p0001 :=
    @g_pw0
  have p0002 :=
    @g_ineq1i (syn_cpw (syn_c0)) (syn_csn (syn_c0)) (syn_c1c) p0001
  have p0003 :=
    @g_disj x (syn_csn (syn_c0)) (syn_c1c) (by exact (show x ∉ ((syn_csn (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))) (by exact (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0004 :=
    @g_n_0nel1c
  have p0005 :=
    @g_elsn x (syn_c0) (by exact (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0006 :=
    @g_eleq1 (.cv x) (syn_c0) (syn_c1c)
  have p0007 :=
    @g_sylbi (.classMem (.cv x) (syn_csn (syn_c0))) (.classEq (.cv x) (syn_c0)) (syn_wb (.classMem (.cv x) (syn_c1c)) (.classMem (syn_c0) (syn_c1c))) p0005 p0006
  have p0008 :=
    @g_mtbiri (.classMem (.cv x) (syn_csn (syn_c0))) (.classMem (.cv x) (syn_c1c)) (.classMem (syn_c0) (syn_c1c)) p0004 p0007
  have p0009 :=
    @g_mprgbir (.classEq (syn_cin (syn_csn (syn_c0)) (syn_c1c)) (syn_c0)) (.neg (.classMem (.cv x) (syn_c1c))) x (syn_csn (syn_c0)) p0003 p0008
  have p0010 :=
    @g_n_3eqtri (syn_cpw1 (syn_c0)) (syn_cin (syn_cpw (syn_c0)) (syn_c1c)) (syn_cin (syn_csn (syn_c0)) (syn_c1c)) (syn_c0) p0000 p0002 p0009
  exact p0010

noncomputable def g_eqpw1
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classEq A (syn_cpw1 B)) (syn_wa (syn_wss A (syn_c1c)) (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_pw1ss1c B
  have p0001 :=
    @g_sseq1 A (syn_cpw1 B) (syn_c1c)
  have p0002 :=
    @g_mpbiri (.classEq A (syn_cpw1 B)) (syn_wss A (syn_c1c)) (syn_wss (syn_cpw1 B) (syn_c1c)) p0000 p0001
  have p0003 :=
    @g_ssofeq y A (syn_cpw1 B) (syn_c1c) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ (B).fv from (by exact fresh_y_not_B))))) (by exact (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0004 :=
    @g_mpan2 (syn_wss A (syn_c1c)) (syn_wss (syn_cpw1 B) (syn_c1c)) (syn_wb (.classEq A (syn_cpw1 B)) (syn_wral y (syn_c1c) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))) p0000 p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral y (syn_c1c) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))))
  have p0006 :=
    @g_el1c x (.cv y) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))
  have p0007 :=
    @g_imbi1i (.classMem (.cv y) (syn_c1c)) (syn_wex x (.classEq (.cv y) (syn_csn (.cv x)))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))) p0006
  have p0008 :=
    @g_n_19_23v (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))) x (by exact (show x ∉ ((syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show x ∉ (((Wff.classMem (.cv y) A)).fv) ∪ (((Wff.classMem (.cv y) (syn_cpw1 B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (.cv y) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv y)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ (A).fv from (by exact dv_A_x)))))) (show x ∉ ((Wff.classMem (.cv y) (syn_cpw1 B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((syn_cpw1 B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (B).fv from (by exact dv_B_x)))))))))))))
  have p0009 :=
    @g_bitr4i (.imp (.classMem (.cv y) (syn_c1c)) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))) (.imp (syn_wex x (.classEq (.cv y) (syn_csn (.cv x)))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))) (.all x (.imp (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))) p0007 p0008
  have p0010 :=
    @g_albii (.imp (.classMem (.cv y) (syn_c1c)) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))) (.all x (.imp (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))) y p0009
  have p0011 :=
    @g_alcom (.imp (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))) x y
  have p0012 :=
    @g_bitr4i (.all y (.imp (.classMem (.cv y) (syn_c1c)) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))) (.all y (.all x (.imp (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))) (.all x (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))) p0010 p0011
  have p0013 :=
    @g_bitri (syn_wral y (syn_c1c) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))) (.all y (.imp (.classMem (.cv y) (syn_c1c)) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))) (.all x (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))) p0005 p0012
  have p0014 :=
    @g_snex (.cv x)
  have p0015 :=
    @g_eleq1 (.cv y) (syn_csn (.cv x)) A
  have p0016 :=
    @g_eleq1 (.cv y) (syn_csn (.cv x)) (syn_cpw1 B)
  have p0017 :=
    @g_bibi12d (.classEq (.cv y) (syn_csn (.cv x))) (.classMem (.cv y) A) (.classMem (syn_csn (.cv x)) A) (.classMem (.cv y) (syn_cpw1 B)) (.classMem (syn_csn (.cv x)) (syn_cpw1 B)) p0015 p0016
  have p0018 :=
    @g_ceqsalv (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))) (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (syn_csn (.cv x)) (syn_cpw1 B))) y (syn_csn (.cv x)) (by exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))) (by exact (show y ∉ ((syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (syn_csn (.cv x)) (syn_cpw1 B)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show y ∉ (((Wff.classMem (syn_csn (.cv x)) A)).fv) ∪ (((Wff.classMem (syn_csn (.cv x)) (syn_cpw1 B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem (syn_csn (.cv x)) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_csn (.cv x))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))) (show y ∉ (A).fv from (by exact fresh_y_not_A)))))) (show y ∉ ((Wff.classMem (syn_csn (.cv x)) (syn_cpw1 B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_csn (.cv x))).fv) ∪ (((syn_cpw1 B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))) (show y ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ (B).fv from (by exact fresh_y_not_B))))))))))))) p0014 p0017
  have p0019 :=
    @g_snelpw1 (.cv x) B
  have p0020 :=
    @g_bibi2i (.classMem (syn_csn (.cv x)) (syn_cpw1 B)) (.classMem (.cv x) B) (.classMem (syn_csn (.cv x)) A) p0019
  have p0021 :=
    @g_bitri (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))) (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (syn_csn (.cv x)) (syn_cpw1 B))) (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)) p0018 p0020
  have p0022 :=
    @g_albii (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))) (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)) x p0021
  have p0023 :=
    @g_bitri (syn_wral y (syn_c1c) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))) (.all x (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x))) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))) (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0013 p0022
  have p0024 :=
    @g_syl6bb (syn_wss A (syn_c1c)) (.classEq A (syn_cpw1 B)) (syn_wral y (syn_c1c) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))) (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0004 p0023
  have p0025 :=
    @g_biadan2 (.classEq A (syn_cpw1 B)) (syn_wss A (syn_c1c)) (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0002 p0024
  exact p0025

noncomputable def g_pw1un
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cpw1 (syn_cun A B)) (syn_cun (syn_cpw1 A) (syn_cpw1 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_rexun (.classEq (.cv x) (syn_csn (.cv y))) y A B
  have p0001 :=
    @g_elpw1 y (.cv x) (syn_cun A B) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B)))))))
  have p0002 :=
    @g_elun (.cv x) (syn_cpw1 A) (syn_cpw1 B)
  have p0003 :=
    @g_elpw1 y (.cv x) A (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0004 :=
    @g_elpw1 y (.cv x) B (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0005 :=
    @g_orbi12i (.classMem (.cv x) (syn_cpw1 A)) (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) (syn_cpw1 B)) (syn_wrex y B (.classEq (.cv x) (syn_csn (.cv y)))) p0003 p0004
  have p0006 :=
    @g_bitri (.classMem (.cv x) (syn_cun (syn_cpw1 A) (syn_cpw1 B))) (syn_wo (.classMem (.cv x) (syn_cpw1 A)) (.classMem (.cv x) (syn_cpw1 B))) (syn_wo (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wrex y B (.classEq (.cv x) (syn_csn (.cv y))))) p0002 p0005
  have p0007 :=
    @g_n_3bitr4i (syn_wrex y (syn_cun A B) (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wo (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wrex y B (.classEq (.cv x) (syn_csn (.cv y))))) (.classMem (.cv x) (syn_cpw1 (syn_cun A B))) (.classMem (.cv x) (syn_cun (syn_cpw1 A) (syn_cpw1 B))) p0000 p0001 p0006
  have p0008 :=
    @g_eqriv x (syn_cpw1 (syn_cun A B)) (syn_cun (syn_cpw1 A) (syn_cpw1 B)) (by exact (show x ∉ ((syn_cpw1 (syn_cun A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))) (by exact (show x ∉ ((syn_cun (syn_cpw1 A) (syn_cpw1 B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ (((syn_cpw1 A)).fv) ∪ (((syn_cpw1 B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))) p0007
  exact p0008

noncomputable def g_pw1in
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cpw1 (syn_cin A B)) (syn_cin (syn_cpw1 A) (syn_cpw1 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_ancom (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B))) (.classEq (.cv x) (syn_csn (.cv y)))
  have p0001 :=
    @g_eleq1 (.cv x) (syn_csn (.cv y)) (syn_cpw1 B)
  have p0002 :=
    @g_snelpw1 (.cv y) B
  have p0003 :=
    @g_syl6bb (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B)) (.classMem (syn_csn (.cv y)) (syn_cpw1 B)) (.classMem (.cv y) B) p0001 p0002
  have p0004 :=
    @g_anbi2d (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B)) (.classMem (.cv y) B) (.classMem (.cv y) A) p0003
  have p0005 :=
    @g_elin (.cv y) A B
  have p0006 :=
    @g_syl6bbr (.classEq (.cv x) (syn_csn (.cv y))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv y) B)) (.classMem (.cv y) (syn_cin A B)) p0004 p0005
  have p0007 :=
    @g_pm5_32ri (.classEq (.cv x) (syn_csn (.cv y))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B))) (.classMem (.cv y) (syn_cin A B)) p0006
  have p0008 :=
    @g_an12 (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B))
  have p0009 :=
    @g_n_3bitr3i (syn_wa (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B))) (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B)))) (syn_wa (.classMem (.cv y) (syn_cin A B)) (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wa (.classMem (.cv y) A) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B)))) p0000 p0007 p0008
  have p0010 :=
    @g_rexbii2 (.classEq (.cv x) (syn_csn (.cv y))) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B))) y (syn_cin A B) A p0009
  have p0011 :=
    @g_elpw1 y (.cv x) (syn_cin A B) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ ((syn_cin A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B)))))))
  have p0012 :=
    @g_elpw1 y (.cv x) A (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0013 :=
    @g_anbi1i (.classMem (.cv x) (syn_cpw1 A)) (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) (syn_cpw1 B)) p0012
  have p0014 :=
    @g_elin (.cv x) (syn_cpw1 A) (syn_cpw1 B)
  have p0015 :=
    @g_r19_41v (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B)) y A (by exact (show y ∉ ((Wff.classMem (.cv x) (syn_cpw1 B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_cpw1 B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))))))))
  have p0016 :=
    @g_n_3bitr4i (syn_wa (.classMem (.cv x) (syn_cpw1 A)) (.classMem (.cv x) (syn_cpw1 B))) (syn_wa (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) (syn_cpw1 B))) (.classMem (.cv x) (syn_cin (syn_cpw1 A) (syn_cpw1 B))) (syn_wrex y A (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B)))) p0013 p0014 p0015
  have p0017 :=
    @g_n_3bitr4i (syn_wrex y (syn_cin A B) (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wrex y A (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B)))) (.classMem (.cv x) (syn_cpw1 (syn_cin A B))) (.classMem (.cv x) (syn_cin (syn_cpw1 A) (syn_cpw1 B))) p0010 p0011 p0016
  have p0018 :=
    @g_eqriv x (syn_cpw1 (syn_cin A B)) (syn_cin (syn_cpw1 A) (syn_cpw1 B)) (by exact (show x ∉ ((syn_cpw1 (syn_cin A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cin A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))) (by exact (show x ∉ ((syn_cin (syn_cpw1 A) (syn_cpw1 B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ (((syn_cpw1 A)).fv) ∪ (((syn_cpw1 B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))) p0017
  exact p0018

noncomputable def g_pw1sn
    (A : Class) (hyp_pw1sn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cpw1 (syn_csn A)) (syn_csn (syn_csn A))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_sneq (.cv y) A
  have p0001 :=
    @g_eqeq2d (.classEq (.cv y) A) (syn_csn (.cv y)) (syn_csn A) (.cv x) p0000
  have p0002 :=
    @g_rexsn (.classEq (.cv x) (syn_csn (.cv y))) (.classEq (.cv x) (syn_csn A)) y A (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ ((Wff.classEq (.cv x) (syn_csn A))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_csn A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))))))) hyp_pw1sn_1 p0001
  have p0003 :=
    @g_elpw1 y (.cv x) (syn_csn A) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
  have p0004 :=
    @g_elsn x (syn_csn A) (by exact (show x ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
  have p0005 :=
    @g_n_3bitr4i (syn_wrex y (syn_csn A) (.classEq (.cv x) (syn_csn (.cv y)))) (.classEq (.cv x) (syn_csn A)) (.classMem (.cv x) (syn_cpw1 (syn_csn A))) (.classMem (.cv x) (syn_csn (syn_csn A))) p0002 p0003 p0004
  have p0006 :=
    @g_eqriv x (syn_cpw1 (syn_csn A)) (syn_csn (syn_csn A)) (by exact (show x ∉ ((syn_cpw1 (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) (by exact (show x ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) p0005
  exact p0006

noncomputable def g_pw10b
    (A : Class) :
    Nominal.NPrf (syn_wb (.classEq (syn_cpw1 A) (syn_c0)) (.classEq A (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_n0 x A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0001 :=
    @g_snelpw1 (.cv x) A
  have p0002 :=
    @g_ne0i (syn_cpw1 A) (syn_csn (.cv x))
  have p0003 :=
    @g_sylbir (.classMem (.cv x) A) (.classMem (syn_csn (.cv x)) (syn_cpw1 A)) (syn_wne (syn_cpw1 A) (syn_c0)) p0001 p0002
  have p0004 :=
    @g_exlimiv (.classMem (.cv x) A) (syn_wne (syn_cpw1 A) (syn_c0)) x (by exact (show x ∉ ((syn_wne (syn_cpw1 A) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show x ∉ (((syn_cpw1 A)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0003
  have p0005 :=
    @g_sylbi (syn_wne A (syn_c0)) (syn_wex x (.classMem (.cv x) A)) (syn_wne (syn_cpw1 A) (syn_c0)) p0000 p0004
  have p0006 :=
    @g_necon4i A (syn_c0) (syn_cpw1 A) (syn_c0) p0005
  have p0007 :=
    @g_pw1eq A (syn_c0)
  have p0008 :=
    @g_pw10
  have p0009 :=
    @g_syl6eq (.classEq A (syn_c0)) (syn_cpw1 A) (syn_cpw1 (syn_c0)) (syn_c0) p0007 p0008
  have p0010 :=
    @g_impbii (.classEq (syn_cpw1 A) (syn_c0)) (.classEq A (syn_c0)) p0006 p0009
  exact p0010



#print axioms g_pw10b

end NFChoice.DirectNominalPrf.WPPReplay
