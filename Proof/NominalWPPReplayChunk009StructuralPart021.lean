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
import NominalWPPReplayChunk009StructuralPart020


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

noncomputable def g_iota4
    (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_weu x ph) (syn_wsbc (syn_cio x ph) x ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have p0000 :=
    Nominal.dfEu x z ph (show x ≠ z from (by exact fresh_x_ne_z)) (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
  have p0001 :=
    @g_bi2 ph (.objEq x z)
  have p0002 :=
    @g_alimi (syn_wb ph (.objEq x z)) (.imp (.objEq x z) ph) x p0001
  have p0003 :=
    @g_sb2 ph x z
  have p0004 :=
    @g_syl (.all x (syn_wb ph (.objEq x z))) (.all x (.imp (.objEq x z) ph)) (syn_wsb z x ph) p0002 p0003
  have p0005 :=
    @g_iotaval ph x z (show x ≠ z from (by exact fresh_x_ne_z))
  have p0006_e00_recanon : Nominal.NPrf (.imp (.all x (syn_wb ph (.objEq x z))) (.classEq (syn_cio x ph) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cio syn_cuni syn_wex syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.all
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
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0006 :=
    @g_eqcomd (.all x (syn_wb ph (.objEq x z))) (syn_cio x ph) (.cv z) p0006_e00_recanon
  have p0007 :=
    @g_dfsbcq2 ph x z (syn_cio x ph)
  have p0008 :=
    @g_syl (.all x (syn_wb ph (.objEq x z))) (.classEq (.cv z) (syn_cio x ph)) (syn_wb (syn_wsb z x ph) (syn_wsbc (syn_cio x ph) x ph)) p0006 p0007
  have p0009 :=
    @g_mpbid (.all x (syn_wb ph (.objEq x z))) (syn_wsb z x ph) (syn_wsbc (syn_cio x ph) x ph) p0004 p0008
  have p0010 :=
    @g_exlimiv (.all x (syn_wb ph (.objEq x z))) (syn_wsbc (syn_cio x ph) x ph) z (by exact (show z ∉ ((syn_wsbc (syn_cio x ph) x ph)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc]; exact (show z ∉ (((syn_cio x ph)).fv) ∪ (((ph).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cio x ph)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio]; exact (show z ∉ ((ph).fv).erase x from (fun hmem => (show z ∉ (ph).fv from (by exact fresh_z_not_ph)) (Finset.mem_of_mem_erase hmem))))) (show z ∉ ((ph).fv).erase x from (fun hmem => (show z ∉ (ph).fv from (by exact fresh_z_not_ph)) (Finset.mem_of_mem_erase hmem)))))))) p0009
  have p0011 :=
    @g_sylbi (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.objEq x z)))) (syn_wsbc (syn_cio x ph) x ph) p0000 p0010
  exact p0011

noncomputable def g_iotabidv
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) (hyp_iotabidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cio x ps) (syn_cio x ch))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var)
  have p0000 :=
    @g_alrimiv ph (syn_wb ps ch) x (by exact (show x ∉ (ph).fv from (by exact dv_ph_x))) hyp_iotabidv_1
  have p0001 :=
    @g_iotabi ps ch x
  have p0002 :=
    @g_syl ph (.all x (syn_wb ps ch)) (.classEq (syn_cio x ps) (syn_cio x ch)) p0000 p0001
  exact p0002

noncomputable def g_iotacl
    (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_weu x ph) (.classMem (syn_cio x ph) (.cab x ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  have p0000 :=
    @g_iota4 ph x
  have p0001 :=
    (by simpa [syn_wb, syn_wsbc] using (Nominal.biimpRefl (syn_wsbc (syn_cio x ph) x ph)))
  have p0002 :=
    @g_sylib (syn_weu x ph) (syn_wsbc (syn_cio x ph) x ph) (.classMem (syn_cio x ph) (.cab x ph)) p0000 p0001
  exact p0002

noncomputable def g_reiotacl2
    (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wreu x A ph) (.classMem (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) (syn_crab x A ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wreu] using (Nominal.biimpRefl (syn_wreu x A ph)))
  have p0001 :=
    @g_iotacl (syn_wa (.classMem (.cv x) A) ph) x
  have p0002 :=
    @g_sylbi (syn_wreu x A ph) (syn_weu x (syn_wa (.classMem (.cv x) A) ph)) (.classMem (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) (.cab x (syn_wa (.classMem (.cv x) A) ph))) p0000 p0001
  have p0003 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A ph)))
  have p0004 :=
    @g_syl6eleqr (syn_wreu x A ph) (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) (.cab x (syn_wa (.classMem (.cv x) A) ph)) (syn_crab x A ph) p0002 p0003
  exact p0004

noncomputable def g_reiotacl
    (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wreu x A ph) (.classMem (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) A)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_ssrab2 ph x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0001 :=
    @g_a1i (syn_wss (syn_crab x A ph) A) (syn_wreu x A ph) p0000
  have p0002 :=
    @g_reiotacl2 ph x A
  have p0003 :=
    @g_sseldd (syn_wreu x A ph) (syn_crab x A ph) A (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) p0001 p0002
  exact p0003

noncomputable def g_iota2df
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (B : Class) (V : Class) (hyp_iota2df_1 : Nominal.NPrf (.imp ph (.classMem B V))) (hyp_iota2df_2 : Nominal.NPrf (.imp ph (syn_weu x ps))) (hyp_iota2df_3 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) B)) (syn_wb ps ch))) (hyp_iota2df_4 : Nominal.NPrf (syn_wnf x ph)) (hyp_iota2df_5 : Nominal.NPrf (.imp ph (syn_wnf x ch))) (hyp_iota2df_6 : Nominal.NPrf (.imp ph (syn_wnfc x B))) :
    Nominal.NPrf (.imp ph (syn_wb ch (.classEq (syn_cio x ps) B))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var) ∪ B.fv ∪ V.fv
  have p0000 :=
    @g_nfiota1 ps x
  have p0001 :=
    @g_a1i (syn_wnfc x (syn_cio x ps)) ph p0000
  have p0002 :=
    @g_nfeqd ph x (syn_cio x ps) B p0001 hyp_iota2df_6
  have p0003 :=
    @g_nfbid ph ch (.classEq (syn_cio x ps) B) x hyp_iota2df_5 p0002
  have p0004 :=
    @g_simpr ph (.classEq (.cv x) B)
  have p0005 :=
    @g_eqeq2d (syn_wa ph (.classEq (.cv x) B)) (.cv x) B (syn_cio x ps) p0004
  have p0006 :=
    @g_bibi12d (syn_wa ph (.classEq (.cv x) B)) ps ch (.classEq (syn_cio x ps) (.cv x)) (.classEq (syn_cio x ps) B) hyp_iota2df_3 p0005
  have p0007 :=
    @g_ex ph (.classEq (.cv x) B) (syn_wb (syn_wb ps (.classEq (syn_cio x ps) (.cv x))) (syn_wb ch (.classEq (syn_cio x ps) B))) p0006
  have p0008 :=
    @g_alrimi ph (.imp (.classEq (.cv x) B) (syn_wb (syn_wb ps (.classEq (syn_cio x ps) (.cv x))) (syn_wb ch (.classEq (syn_cio x ps) B)))) x hyp_iota2df_4 p0007
  have p0009 :=
    @g_iota1 ps x
  have p0010 :=
    @g_syl ph (syn_weu x ps) (syn_wb ps (.classEq (syn_cio x ps) (.cv x))) hyp_iota2df_2 p0009
  have p0011 :=
    @g_alrimi ph (syn_wb ps (.classEq (syn_cio x ps) (.cv x))) x hyp_iota2df_4 p0010
  have p0012 :=
    @g_vtoclgft (syn_wb ps (.classEq (syn_cio x ps) (.cv x))) (syn_wb ch (.classEq (syn_cio x ps) B)) x B V
  have p0013 :=
    @g_syl221anc ph (syn_wnfc x B) (syn_wnf x (syn_wb ch (.classEq (syn_cio x ps) B))) (.all x (.imp (.classEq (.cv x) B) (syn_wb (syn_wb ps (.classEq (syn_cio x ps) (.cv x))) (syn_wb ch (.classEq (syn_cio x ps) B))))) (.all x (syn_wb ps (.classEq (syn_cio x ps) (.cv x)))) (.classMem B V) (syn_wb ch (.classEq (syn_cio x ps) B)) hyp_iota2df_6 p0003 p0008 p0011 hyp_iota2df_1 p0012
  exact p0013

noncomputable def g_iota2
    (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv) (hyp_iota2_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A B) (syn_weu x ph)) (syn_wb ps (.classEq (syn_cio x ph) A))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_elex A B
  have p0001 :=
    @g_simpl (.classMem A (syn_cvv)) (syn_weu x ph)
  have p0002 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_weu x ph)
  have p0003 :=
    @g_adantl (.classEq (.cv x) A) (syn_wb ph ps) (syn_wa (.classMem A (syn_cvv)) (syn_weu x ph)) hyp_iota2_1
  have p0004 :=
    @g_nfv (.classMem A (syn_cvv)) x (by exact (show x ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))
  have p0005 :=
    @g_nfeu1 ph x
  have p0006 :=
    @g_nfan (.classMem A (syn_cvv)) (syn_weu x ph) x p0004 p0005
  have p0007 :=
    @g_nfvd (syn_wa (.classMem A (syn_cvv)) (syn_weu x ph)) ps x (by exact (show x ∉ (ps).fv from (by exact dv_ps_x)))
  have p0008 :=
    @g_nfcvd (syn_wa (.classMem A (syn_cvv)) (syn_weu x ph)) x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0009 :=
    @g_iota2df (syn_wa (.classMem A (syn_cvv)) (syn_weu x ph)) ph ps x A (syn_cvv) p0001 p0002 p0003 p0006 p0007 p0008
  have p0010 :=
    @g_sylan (.classMem A B) (.classMem A (syn_cvv)) (syn_weu x ph) (syn_wb ps (.classEq (syn_cio x ph) A)) p0000 p0009
  exact p0010

noncomputable def g_reiota2
    (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (hyp_reiota2_1 : Nominal.NPrf (.imp (.classEq (.cv x) B) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (syn_wa (.classMem B A) (syn_wreu x A ph)) (syn_wb ps (.classEq (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) B))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_simpl (.classMem B A) (syn_wreu x A ph)
  have p0001 :=
    @g_biantrurd (syn_wa (.classMem B A) (syn_wreu x A ph)) (.classMem B A) ps p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wreu] using (Nominal.biimpRefl (syn_wreu x A ph)))
  have p0003 :=
    @g_eleq1 (.cv x) B A
  have p0004 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) A) (.classMem B A) ph ps p0003 hyp_reiota2_1
  have p0005 :=
    @g_iota2 (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem B A) ps) x B A (by exact (show x ∉ (B).fv from (by exact dv_B_x))) (by exact (show x ∉ ((syn_wa (.classMem B A) ps)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classMem B A)).fv) ∪ ((ps).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem B A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((B).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact dv_B_x)) (show x ∉ (A).fv from (by exact dv_A_x)))))) (show x ∉ (ps).fv from (by exact dv_ps_x))))))) p0004
  have p0006 :=
    @g_sylan2b (syn_wreu x A ph) (.classMem B A) (syn_weu x (syn_wa (.classMem (.cv x) A) ph)) (syn_wb (syn_wa (.classMem B A) ps) (.classEq (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) B)) p0002 p0005
  have p0007 :=
    @g_bitrd (syn_wa (.classMem B A) (syn_wreu x A ph)) ps (syn_wa (.classMem B A) ps) (.classEq (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) B) p0001 p0006
  exact p0007



#print axioms g_reiota2

end NFChoice.DirectNominalPrf.WPPReplay
