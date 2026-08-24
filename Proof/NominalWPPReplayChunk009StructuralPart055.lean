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
import NominalWPPReplayChunk009StructuralPart054


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

noncomputable def g_tfin11
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N)) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
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
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_p : a ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have fresh_b_ne_p : b ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_b : p ≠ b :=
    Ne.symm fresh_b_ne_p
  have p0000 :=
    @g_tfinnnul M
  have p0001 :=
    @g_ex (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wne (syn_ctfin M) (syn_c0)) p0000
  have p0002 :=
    @g_necon4d (.classMem M (syn_cnnc)) M (syn_c0) (syn_ctfin M) (syn_c0) p0001
  have p0003 :=
    @g_n_3ad2ant1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.imp (.classEq (syn_ctfin M) (syn_c0)) (.classEq M (syn_c0))) (.classEq (syn_ctfin M) (syn_ctfin N)) p0002
  have p0004 :=
    @g_impcom (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq (syn_ctfin M) (syn_c0)) (.classEq M (syn_c0)) p0003
  have p0005 :=
    @g_eqeq1 (syn_ctfin M) (syn_ctfin N) (syn_c0)
  have p0006 :=
    @g_adantl (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_wb (.classEq (syn_ctfin M) (syn_c0)) (.classEq (syn_ctfin N) (syn_c0))) (.classMem N (syn_cnnc)) p0005
  have p0007 :=
    @g_tfinnnul N
  have p0008 :=
    @g_ex (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) (syn_wne (syn_ctfin N) (syn_c0)) p0007
  have p0009 :=
    @g_necon4d (.classMem N (syn_cnnc)) N (syn_c0) (syn_ctfin N) (syn_c0) p0008
  have p0010 :=
    @g_adantr (.classMem N (syn_cnnc)) (.imp (.classEq (syn_ctfin N) (syn_c0)) (.classEq N (syn_c0))) (.classEq (syn_ctfin M) (syn_ctfin N)) p0009
  have p0011 :=
    @g_sylbid (syn_wa (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq (syn_ctfin M) (syn_c0)) (.classEq (syn_ctfin N) (syn_c0)) (.classEq N (syn_c0)) p0006 p0010
  have p0012 :=
    @g_n_3adant1 (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)) (.imp (.classEq (syn_ctfin M) (syn_c0)) (.classEq N (syn_c0))) (.classMem M (syn_cnnc)) p0011
  have p0013 :=
    @g_impcom (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq (syn_ctfin M) (syn_c0)) (.classEq N (syn_c0)) p0012
  have p0014 :=
    @g_eqtr4d (syn_wa (.classEq (syn_ctfin M) (syn_c0)) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) M (syn_c0) N p0004 p0013
  have p0015 :=
    @g_ex (.classEq (syn_ctfin M) (syn_c0)) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N) p0014
  have p0016 :=
    @g_neeq1 (syn_ctfin M) (syn_ctfin N) (syn_c0)
  have p0017 :=
    @g_biimpd (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_wne (syn_ctfin M) (syn_c0)) (syn_wne (syn_ctfin N) (syn_c0)) p0016
  have p0018 :=
    @g_ancld (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_wne (syn_ctfin M) (syn_c0)) (syn_wne (syn_ctfin N) (syn_c0)) p0017
  have p0019 :=
    @g_tfineq M (syn_c0)
  have p0020 :=
    @g_tfinnul
  have p0021 :=
    @g_syl6eq (.classEq M (syn_c0)) (syn_ctfin M) (syn_ctfin (syn_c0)) (syn_c0) p0019 p0020
  have p0022 :=
    @g_necon3i M (syn_c0) (syn_ctfin M) (syn_c0) p0021
  have p0023 :=
    @g_tfineq N (syn_c0)
  have p0024 :=
    @g_tfinnul
  have p0025 :=
    @g_syl6eq (.classEq N (syn_c0)) (syn_ctfin N) (syn_ctfin (syn_c0)) (syn_c0) p0023 p0024
  have p0026 :=
    @g_necon3i N (syn_c0) (syn_ctfin N) (syn_c0) p0025
  have p0027 :=
    @g_anim12i (syn_wne (syn_ctfin M) (syn_c0)) (syn_wne M (syn_c0)) (syn_wne (syn_ctfin N) (syn_c0)) (syn_wne N (syn_c0)) p0022 p0026
  have p0028 :=
    @g_syl6 (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_wne (syn_ctfin M) (syn_c0)) (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wne (syn_ctfin N) (syn_c0))) (syn_wa (syn_wne M (syn_c0)) (syn_wne N (syn_c0))) p0018 p0027
  have p0029 :=
    @g_n_3ad2ant3 (.classEq (syn_ctfin M) (syn_ctfin N)) (.classMem M (syn_cnnc)) (.imp (syn_wne (syn_ctfin M) (syn_c0)) (syn_wa (syn_wne M (syn_c0)) (syn_wne N (syn_c0)))) (.classMem N (syn_cnnc)) p0028
  have p0030 :=
    @g_tfinprop M a (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
  have p0031 :=
    @g_ex (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)))) p0030
  have p0032 :=
    @g_n_3ad2ant1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.imp (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))))) (.classEq (syn_ctfin M) (syn_ctfin N)) p0031
  have p0033 :=
    @g_tfinprop N b (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N)))
  have p0034 :=
    @g_ex (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) (syn_wa (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))) p0033
  have p0035 :=
    @g_n_3ad2ant2 (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc)) (.imp (syn_wne N (syn_c0)) (syn_wa (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))))) (.classEq (syn_ctfin M) (syn_ctfin N)) p0034
  have p0036 :=
    @g_reeanv (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)) a b M N (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) (by exact (show b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_ctfin M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))))) (show b ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show b ∉ (M).fv from (by exact fresh_b_not_M))))))))) (by exact (show a ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((syn_ctfin N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cpw1 (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show a ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ b from (by exact fresh_a_ne_b)))))))) (show a ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show a ∉ (N).fv from (by exact fresh_a_not_N))))))))) (show a ≠ b from (by exact fresh_a_ne_b))
  have p0037 :=
    @g_simp31 (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))
  have p0038 :=
    @g_tfincl M
  have p0039 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (.classMem M (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc)) p0037 p0038
  have p0040 :=
    @g_simp2l (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))
  have p0041 :=
    @g_simp2r (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))
  have p0042 :=
    @g_simp33 (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))
  have p0043 :=
    @g_eleqtrrd (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (syn_cpw1 (.cv b)) (syn_ctfin N) (syn_ctfin M) p0041 p0042
  have p0044 :=
    @g_ncfinlower (.cv a) (.cv b) p (syn_ctfin M) (by exact (show p ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ a from (by exact fresh_p_ne_a))))))) (by exact (show p ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ b from (by exact fresh_p_ne_b)))))))
  have p0045_e03_recanon : Nominal.NPrf (.imp (syn_w3a (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))) (syn_wrex p (syn_cnnc) (syn_wa (.objMem a p) (.objMem b p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_ctfin syn_cif syn_wo syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn syn_cnnc syn_cint syn_cpw1 syn_wrex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0044
  have p0045 :=
    @g_syl3anc (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) (syn_wrex p (syn_cnnc) (syn_wa (.objMem a p) (.objMem b p))) p0039 p0040 p0043 p0045_e03_recanon
  have p0046 :=
    @g_simpl31 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))
  have p0047 :=
    @g_simprl (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p))
  have p0048 :=
    @g_simpl1l (.classMem (.cv a) M) (.classMem (.cv b) N) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))
  have p0049 :=
    @g_simprrl (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (.classMem (.cv p) (syn_cnnc)) (.objMem a p) (.objMem b p)
  have p0050 :=
    @g_nnceleq (.cv a) M (.cv p)
  have p0051_e04_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))) (syn_wa (.classMem (.cv a) M) (.objMem a p))) (.classEq M (.cv p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0050
  have p0051 :=
    @g_syl22anc (syn_wa (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))) (.classMem M (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)) (.classMem (.cv a) M) (.objMem a p) (.classEq M (.cv p)) p0046 p0047 p0048 p0049 p0051_e04_recanon
  have p0052 :=
    @g_simpl32 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))
  have p0053 :=
    @g_simpl1r (.classMem (.cv a) M) (.classMem (.cv b) N) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))
  have p0054 :=
    @g_simprrr (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (.classMem (.cv p) (syn_cnnc)) (.objMem a p) (.objMem b p)
  have p0055 :=
    @g_nnceleq (.cv b) N (.cv p)
  have p0056_e04_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))) (syn_wa (.classMem (.cv b) N) (.objMem b p))) (.classEq N (.cv p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0055
  have p0056 :=
    @g_syl22anc (syn_wa (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))) (.classMem N (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)) (.classMem (.cv b) N) (.objMem b p) (.classEq N (.cv p)) p0052 p0047 p0053 p0054 p0056_e04_recanon
  have p0057 :=
    @g_eqtr4d (syn_wa (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))) M (.cv p) N p0051 p0056
  have p0058 :=
    @g_expr (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)) (.classEq M N) p0057
  have p0059 :=
    @g_rexlimdva (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (syn_wa (.objMem a p) (.objMem b p)) (.classEq M N) p (syn_cnnc) (by exact (show p ∉ ((Wff.classEq M N)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (M).fv from (by exact fresh_p_not_M)) (show p ∉ (N).fv from (by exact fresh_p_not_N))))))) (by exact (show p ∉ ((syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show p ∉ (((syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))).fv) ∪ (((syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))).fv) ∪ (((syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show p ∉ (((Wff.classEq (syn_ctfin M) (syn_ctfin N))).fv) ∪ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.classEq (syn_ctfin M) (syn_ctfin N))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ (((syn_ctfin M)).fv) ∪ (((syn_ctfin N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show p ∉ (M).fv from (by exact fresh_p_not_M)))) (show p ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show p ∉ (N).fv from (by exact fresh_p_not_N)))))))) (show p ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (M).fv from (by exact fresh_p_not_M)) (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show p ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (N).fv from (by exact fresh_p_not_N)) (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show p ∉ ((syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show p ∉ (((Wff.classMem (.cv a) M)).fv) ∪ (((Wff.classMem (.cv b) N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.classMem (.cv a) M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ (((Class.cv a)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ a from (by exact fresh_p_ne_a)))))) (show p ∉ (M).fv from (by exact fresh_p_not_M)))))) (show p ∉ ((Wff.classMem (.cv b) N)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ (((Class.cv b)).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ b from (by exact fresh_p_ne_b)))))) (show p ∉ (N).fv from (by exact fresh_p_not_N))))))))))) (show p ∉ ((syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show p ∉ (((Wff.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))).fv) ∪ (((Wff.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_ctfin M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show p ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ a from (by exact fresh_p_ne_a)))))))) (show p ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show p ∉ (M).fv from (by exact fresh_p_not_M)))))))) (show p ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((syn_ctfin N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cpw1 (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show p ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ b from (by exact fresh_p_ne_b)))))))) (show p ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show p ∉ (N).fv from (by exact fresh_p_not_N))))))))))))))))) p0058
  have p0060 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))) (syn_wrex p (syn_cnnc) (syn_wa (.objMem a p) (.objMem b p))) (.classEq M N) p0045 p0059
  have p0061 :=
    @g_n_3exp (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N) p0060
  have p0062 :=
    @g_rexlimivv (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N)) a b M N (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) (by exact (show a ∉ ((Wff.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show a ∉ (((syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))).fv) ∪ (((Wff.classEq M N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show a ∉ (((Wff.classEq (syn_ctfin M) (syn_ctfin N))).fv) ∪ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classEq (syn_ctfin M) (syn_ctfin N))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_ctfin M)).fv) ∪ (((syn_ctfin N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))) (show a ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))))))) (show a ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show a ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (N).fv from (by exact fresh_a_not_N)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show a ∉ ((Wff.classEq M N)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ (N).fv from (by exact fresh_a_not_N))))))))))) (by exact (show b ∉ ((Wff.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))).fv) ∪ (((Wff.classEq M N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show b ∉ (((Wff.classEq (syn_ctfin M) (syn_ctfin N))).fv) ∪ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classEq (syn_ctfin M) (syn_ctfin N))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((syn_ctfin M)).fv) ∪ (((syn_ctfin N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))) (show b ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show b ∉ (N).fv from (by exact fresh_b_not_N)))))))) (show b ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (M).fv from (by exact fresh_b_not_M)) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show b ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (N).fv from (by exact fresh_b_not_N)) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show b ∉ ((Wff.classEq M N)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (M).fv from (by exact fresh_b_not_M)) (show b ∉ (N).fv from (by exact fresh_b_not_N))))))))))) (show a ≠ b from (by exact fresh_a_ne_b)) p0061
  have p0063 :=
    @g_sylbir (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))) (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))) (syn_wrex a M (syn_wrex b N (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))))) (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N)) p0036 p0062
  have p0064 :=
    @g_ad2ant2l (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))) (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))) (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N)) (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) p0063
  have p0065 :=
    @g_com12 (syn_wa (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)))) (syn_wa (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N) p0064
  have p0066 :=
    @g_syl2and (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)))) (syn_wne N (syn_c0)) (syn_wa (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))) (.classEq M N) p0032 p0035 p0065
  have p0067 :=
    @g_syld (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (syn_wne (syn_ctfin M) (syn_c0)) (syn_wa (syn_wne M (syn_c0)) (syn_wne N (syn_c0))) (.classEq M N) p0029 p0066
  have p0068 :=
    @g_com12 (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (syn_wne (syn_ctfin M) (syn_c0)) (.classEq M N) p0067
  have p0069 :=
    @g_pm2_61ine (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N)) (syn_ctfin M) (syn_c0) p0015 p0068
  exact p0069

noncomputable def g_tfinpw1
    (A : Class) (M : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (.classMem (syn_cpw1 A) (syn_ctfin M))) := by
  let proofSupport : Finset Var := A.fv ∪ M.fv
  let b : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_b_ne_n : b ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_b : n ≠ b :=
    Ne.symm fresh_b_ne_n
  have p0000 :=
    @g_ne0i M A
  have p0001 :=
    @g_tfinprop M b (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
  have p0002 :=
    @g_sylan2 (.classMem A M) (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))) p0000 p0001
  have p0003 :=
    @g_ncfinraise A (.cv b) n M (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A))) (by exact (show n ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ b from (by exact fresh_n_ne_b)))))))
  have p0004 :=
    @g_n_3expa (.classMem M (syn_cnnc)) (.classMem A M) (.classMem (.cv b) M) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)))) p0003
  have p0005 :=
    @g_adantrr (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (.classMem (.cv b) M) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)))) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) p0004
  have p0006 :=
    @g_simp3rl (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)) (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
  have p0007 :=
    @g_simp3l (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)))
  have p0008 :=
    @g_simp1l (.classMem M (syn_cnnc)) (.classMem A M) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))
  have p0009 :=
    @g_tfincl M
  have p0010 :=
    @g_syl (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))) (.classMem M (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc)) p0008 p0009
  have p0011 :=
    @g_simp3rr (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)) (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
  have p0012 :=
    @g_simp2r (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))
  have p0013 :=
    @g_nnceleq (syn_cpw1 (.cv b)) (.cv n) (syn_ctfin M)
  have p0014 :=
    @g_syl22anc (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_cpw1 (.cv b)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) (.classEq (.cv n) (syn_ctfin M)) p0007 p0010 p0011 p0012 p0013
  have p0015 :=
    @g_eleqtrd (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))) (syn_cpw1 A) (.cv n) (syn_ctfin M) p0006 p0014
  have p0016 :=
    @g_n_3expa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)))) (.classMem (syn_cpw1 A) (syn_ctfin M)) p0015
  have p0017 :=
    @g_expr (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))) (.classMem (syn_cpw1 A) (syn_ctfin M)) p0016
  have p0018 :=
    @g_rexlimdva (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))) (.classMem (syn_cpw1 A) (syn_ctfin M)) n (syn_cnnc) (by exact (show n ∉ ((Wff.classMem (syn_cpw1 A) (syn_ctfin M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((syn_cpw1 A)).fv) ∪ (((syn_ctfin M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show n ∉ (A).fv from (by exact fresh_n_not_A)))) (show n ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show n ∉ (M).fv from (by exact fresh_n_not_M))))))))) (by exact (show n ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show n ∉ (((syn_wa (.classMem M (syn_cnnc)) (.classMem A M))).fv) ∪ (((syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem A M))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show n ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem A M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (M).fv from (by exact fresh_n_not_M)) (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show n ∉ ((Wff.classMem A M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ ((A).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (A).fv from (by exact fresh_n_not_A)) (show n ∉ (M).fv from (by exact fresh_n_not_M)))))))))) (show n ∉ ((syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show n ∉ (((Wff.classMem (.cv b) M)).fv) ∪ (((Wff.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Wff.classMem (.cv b) M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((Class.cv b)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ b from (by exact fresh_n_ne_b)))))) (show n ∉ (M).fv from (by exact fresh_n_not_M)))))) (show n ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((syn_ctfin M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cpw1 (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show n ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ b from (by exact fresh_n_ne_b)))))))) (show n ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show n ∉ (M).fv from (by exact fresh_n_not_M))))))))))))))))) p0017
  have p0019 :=
    @g_mpd (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)))) (.classMem (syn_cpw1 A) (syn_ctfin M)) p0005 p0018
  have p0020 :=
    @g_expr (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) (.classMem (syn_cpw1 A) (syn_ctfin M)) p0019
  have p0021 :=
    @g_rexlimdva (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) (.classMem (syn_cpw1 A) (syn_ctfin M)) b M (by exact (show b ∉ ((Wff.classMem (syn_cpw1 A) (syn_ctfin M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cpw1 A)).fv) ∪ (((syn_ctfin M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))) (show b ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show b ∉ (M).fv from (by exact fresh_b_not_M))))))))) (by exact (show b ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem A M))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem A M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (M).fv from (by exact fresh_b_not_M)) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classMem A M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((A).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (A).fv from (by exact fresh_b_not_A)) (show b ∉ (M).fv from (by exact fresh_b_not_M))))))))))) p0020
  have p0022 :=
    @g_adantld (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))) (.classMem (syn_cpw1 A) (syn_ctfin M)) (.classMem (syn_ctfin M) (syn_cnnc)) p0021
  have p0023 :=
    @g_mpd (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))) (.classMem (syn_cpw1 A) (syn_ctfin M)) p0002 p0022
  exact p0023

noncomputable def g_ncfintfin
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classEq (syn_ctfin (syn_cncfin A)) (syn_cncfin (syn_cpw1 A)))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_ncfinprop A V
  have p0001 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)) p0000
  have p0002 :=
    @g_tfincl (syn_cncfin A)
  have p0003 :=
    @g_syl (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem (syn_ctfin (syn_cncfin A)) (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_pw1exg A V
  have p0005 :=
    @g_ncfinprop (syn_cpw1 A) (syn_cvv)
  have p0006 :=
    @g_sylan2 (.classMem A V) (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cpw1 A) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_cpw1 A)) (syn_cnnc)) (.classMem (syn_cpw1 A) (syn_cncfin (syn_cpw1 A)))) p0004 p0005
  have p0007 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem (syn_cncfin (syn_cpw1 A)) (syn_cnnc)) (.classMem (syn_cpw1 A) (syn_cncfin (syn_cpw1 A))) p0006
  have p0008 :=
    @g_tfinpw1 A (syn_cncfin A)
  have p0009 :=
    @g_syl (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (syn_wa (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A))) (.classMem (syn_cpw1 A) (syn_ctfin (syn_cncfin A))) p0000 p0008
  have p0010 :=
    @g_simprd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem (syn_cncfin (syn_cpw1 A)) (syn_cnnc)) (.classMem (syn_cpw1 A) (syn_cncfin (syn_cpw1 A))) p0006
  have p0011 :=
    @g_nnceleq (syn_cpw1 A) (syn_ctfin (syn_cncfin A)) (syn_cncfin (syn_cpw1 A))
  have p0012 :=
    @g_syl22anc (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem (syn_ctfin (syn_cncfin A)) (syn_cnnc)) (.classMem (syn_cncfin (syn_cpw1 A)) (syn_cnnc)) (.classMem (syn_cpw1 A) (syn_ctfin (syn_cncfin A))) (.classMem (syn_cpw1 A) (syn_cncfin (syn_cpw1 A))) (.classEq (syn_ctfin (syn_cncfin A)) (syn_cncfin (syn_cpw1 A))) p0003 p0007 p0009 p0010 p0011
  exact p0012



#print axioms g_ncfintfin

end NFChoice.DirectNominalPrf.WPPReplay
