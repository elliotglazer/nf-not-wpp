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
import NominalWPPReplayChunk009StructuralPart032


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

noncomputable def g_nnsucelrlem2
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.neg (.classMem B A)) (.classEq (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B)) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_eldifsn (.cv x) (syn_cun A (syn_csn B)) B
  have p0001 :=
    @g_elun (.cv x) A (syn_csn B)
  have p0002 :=
    @g_elsn x B (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0003 :=
    @g_orbi2i (.classMem (.cv x) (syn_csn B)) (.classEq (.cv x) B) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_bitri (.classMem (.cv x) (syn_cun A (syn_csn B))) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn B))) (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) B)) p0001 p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv x) B)))
  have p0006 :=
    @g_anbi12i (.classMem (.cv x) (syn_cun A (syn_csn B))) (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) B)) (syn_wne (.cv x) B) (.neg (.classEq (.cv x) B)) p0004 p0005
  have p0007 :=
    @g_pm5_61 (.classMem (.cv x) A) (.classEq (.cv x) B)
  have p0008 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B))) (syn_wa (.classMem (.cv x) (syn_cun A (syn_csn B))) (syn_wne (.cv x) B)) (syn_wa (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) B)) (.neg (.classEq (.cv x) B))) (syn_wa (.classMem (.cv x) A) (.neg (.classEq (.cv x) B))) p0000 p0006 p0007
  have p0009 :=
    @g_ancom (.classMem (.cv x) A) (.neg (.classEq (.cv x) B))
  have p0010 :=
    @g_bitri (.classMem (.cv x) (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B))) (syn_wa (.classMem (.cv x) A) (.neg (.classEq (.cv x) B))) (syn_wa (.neg (.classEq (.cv x) B)) (.classMem (.cv x) A)) p0008 p0009
  have p0011 :=
    @g_eleq1 (.cv x) B A
  have p0012 :=
    @g_biimpcd (.classEq (.cv x) B) (.classMem (.cv x) A) (.classMem B A) p0011
  have p0013 :=
    @g_con3d (.classMem (.cv x) A) (.classEq (.cv x) B) (.classMem B A) p0012
  have p0014 :=
    @g_com12 (.classMem (.cv x) A) (.neg (.classMem B A)) (.neg (.classEq (.cv x) B)) p0013
  have p0015 :=
    @g_pm4_71rd (.neg (.classMem B A)) (.classMem (.cv x) A) (.neg (.classEq (.cv x) B)) p0014
  have p0016 :=
    @g_bicomd (.neg (.classMem B A)) (.classMem (.cv x) A) (syn_wa (.neg (.classEq (.cv x) B)) (.classMem (.cv x) A)) p0015
  have p0017 :=
    @g_syl5bb (.classMem (.cv x) (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B))) (syn_wa (.neg (.classEq (.cv x) B)) (.classMem (.cv x) A)) (.neg (.classMem B A)) (.classMem (.cv x) A) p0010 p0016
  have p0018 :=
    @g_eqrdv (.neg (.classMem B A)) x (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B)) A (by exact (show x ∉ ((syn_cdif (syn_cun A (syn_csn B)) (syn_csn B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show x ∉ (((syn_cun A (syn_csn B))).fv) ∪ (((syn_csn B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cun A (syn_csn B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ ((A).fv) ∪ (((syn_csn B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))))))) (show x ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((Wff.neg (.classMem B A))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show x ∉ ((Wff.classMem B A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((B).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (A).fv from (by exact fresh_x_not_A))))))))) p0017
  exact p0018

noncomputable def g_nnsucelrlem3
    (A : Class) (B : Class) (X : Class) (Y : Class) (hyp_nnsucelrlem3_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (.imp (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) (.neg (.classMem Y B))) (.classEq B (syn_cun (syn_cdif A (syn_csn Y)) (syn_csn X)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ X.fv ∪ Y.fv
  have p0000 :=
    @g_indir B (syn_csn Y) (syn_ccompl (syn_csn Y))
  have p0001 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif B (syn_csn Y))))
  have p0002 :=
    @g_eqcomi (syn_cdif B (syn_csn Y)) (syn_cin B (syn_ccompl (syn_csn Y))) p0001
  have p0003 :=
    @g_incompl (syn_csn Y)
  have p0004 :=
    @g_uneq12i (syn_cin B (syn_ccompl (syn_csn Y))) (syn_cdif B (syn_csn Y)) (syn_cin (syn_csn Y) (syn_ccompl (syn_csn Y))) (syn_c0) p0002 p0003
  have p0005 :=
    @g_un0 (syn_cdif B (syn_csn Y))
  have p0006 :=
    @g_eqtri (syn_cun (syn_cin B (syn_ccompl (syn_csn Y))) (syn_cin (syn_csn Y) (syn_ccompl (syn_csn Y)))) (syn_cun (syn_cdif B (syn_csn Y)) (syn_c0)) (syn_cdif B (syn_csn Y)) p0004 p0005
  have p0007 :=
    @g_eqtri (syn_cin (syn_cun B (syn_csn Y)) (syn_ccompl (syn_csn Y))) (syn_cun (syn_cin B (syn_ccompl (syn_csn Y))) (syn_cin (syn_csn Y) (syn_ccompl (syn_csn Y)))) (syn_cdif B (syn_csn Y)) p0000 p0006
  have p0008 :=
    @g_difsn Y B
  have p0009 :=
    @g_n_3ad2ant3 (.neg (.classMem Y B)) (syn_wne X Y) (.classEq (syn_cdif B (syn_csn Y)) B) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) p0008
  have p0010 :=
    @g_syl5req (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) (.neg (.classMem Y B))) (syn_cin (syn_cun B (syn_csn Y)) (syn_ccompl (syn_csn Y))) (syn_cdif B (syn_csn Y)) B p0007 p0009
  have p0011 :=
    @g_simp2 (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) (.neg (.classMem Y B))
  have p0012 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne X Y)))
  have p0013 :=
    @g_biimpi (syn_wne X Y) (.neg (.classEq X Y)) p0012
  have p0014 :=
    @g_n_3ad2ant1 (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) (.neg (.classEq X Y)) (.neg (.classMem Y B)) p0013
  have p0015 :=
    @g_elcompl X (syn_csn Y) hyp_nnsucelrlem3_1
  have p0016 :=
    @g_elsnc X Y hyp_nnsucelrlem3_1
  have p0017 :=
    @g_xchbinx (.classMem X (syn_ccompl (syn_csn Y))) (.classMem X (syn_csn Y)) (.classEq X Y) p0015 p0016
  have p0018 :=
    @g_snss X (syn_ccompl (syn_csn Y)) hyp_nnsucelrlem3_1
  have p0019 :=
    @g_bitr3i (.neg (.classEq X Y)) (.classMem X (syn_ccompl (syn_csn Y))) (syn_wss (syn_csn X) (syn_ccompl (syn_csn Y))) p0017 p0018
  have p0020 :=
    @g_sylib (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) (.neg (.classMem Y B))) (.neg (.classEq X Y)) (syn_wss (syn_csn X) (syn_ccompl (syn_csn Y))) p0014 p0019
  have p0021 :=
    @g_ssequn2 (syn_csn X) (syn_ccompl (syn_csn Y))
  have p0022 :=
    @g_sylib (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) (.neg (.classMem Y B))) (syn_wss (syn_csn X) (syn_ccompl (syn_csn Y))) (.classEq (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X)) (syn_ccompl (syn_csn Y))) p0020 p0021
  have p0023 :=
    @g_ineq12d (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) (.neg (.classMem Y B))) (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)) (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X)) (syn_ccompl (syn_csn Y)) p0011 p0022
  have p0024 :=
    @g_eqtr4d (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) (.neg (.classMem Y B))) B (syn_cin (syn_cun B (syn_csn Y)) (syn_ccompl (syn_csn Y))) (syn_cin (syn_cun A (syn_csn X)) (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X))) p0010 p0023
  have p0025 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif A (syn_csn Y))))
  have p0026 :=
    @g_uneq1i (syn_cdif A (syn_csn Y)) (syn_cin A (syn_ccompl (syn_csn Y))) (syn_csn X) p0025
  have p0027 :=
    @g_undir A (syn_ccompl (syn_csn Y)) (syn_csn X)
  have p0028 :=
    @g_eqtri (syn_cun (syn_cdif A (syn_csn Y)) (syn_csn X)) (syn_cun (syn_cin A (syn_ccompl (syn_csn Y))) (syn_csn X)) (syn_cin (syn_cun A (syn_csn X)) (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X))) p0026 p0027
  have p0029 :=
    @g_syl6eqr (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) (.neg (.classMem Y B))) B (syn_cin (syn_cun A (syn_csn X)) (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X))) (syn_cun (syn_cdif A (syn_csn Y)) (syn_csn X)) p0024 p0028
  exact p0029

noncomputable def g_nnsucelrlem4
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classEq (syn_cun (syn_cdif B (syn_csn A)) (syn_csn A)) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_undif1 B (syn_csn A)
  have p0001 :=
    @g_snssi A B
  have p0002 :=
    @g_ssequn2 (syn_csn A) B
  have p0003 :=
    @g_sylib (.classMem A B) (syn_wss (syn_csn A) B) (.classEq (syn_cun B (syn_csn A)) B) p0001 p0002
  have p0004 :=
    @g_syl5eq (.classMem A B) (syn_cun (syn_cdif B (syn_csn A)) (syn_csn A)) (syn_cun B (syn_csn A)) B p0000 p0003
  exact p0004



#print axioms g_nnsucelrlem4

end NFChoice.DirectNominalPrf.WPPReplay
