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
import NominalWPPReplayChunk009StructuralPart038


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

noncomputable def g_preaddccan2
    (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wne (syn_cplc M N) (syn_c0))) (syn_wb (.classEq (syn_cplc M N) (syn_cplc M P)) (.classEq N P))) := by
  let proofSupport : Finset Var := P.fv ∪ M.fv ∪ N.fv
  let m : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_P : m ∉ P.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_not_P : k ∉ P.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_not_N : k ∉ N.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_m_ne_k : m ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_m : k ≠ m :=
    Ne.symm fresh_m_ne_k
  have p0000 :=
    @g_preaddccan2lem1 P m N (by exact (show m ∉ (N).fv from (by exact fresh_m_not_N))) (by exact (show m ∉ (P).fv from (by exact fresh_m_not_P)))
  have p0001 :=
    @g_addceq1 (.cv m) (syn_c0c) N
  have p0002 :=
    @g_neeq1d (.classEq (.cv m) (syn_c0c)) (syn_cplc (.cv m) N) (syn_cplc (syn_c0c) N) (syn_c0) p0001
  have p0003 :=
    @g_addceq1 (.cv m) (syn_c0c) P
  have p0004 :=
    @g_eqeq12d (.classEq (.cv m) (syn_c0c)) (syn_cplc (.cv m) N) (syn_cplc (syn_c0c) N) (syn_cplc (.cv m) P) (syn_cplc (syn_c0c) P) p0001 p0003
  have p0005 :=
    @g_anbi12d (.classEq (.cv m) (syn_c0c)) (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (syn_wne (syn_cplc (syn_c0c) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)) (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P)) p0002 p0004
  have p0006 :=
    @g_imbi1d (.classEq (.cv m) (syn_c0c)) (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0)) (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P))) (.classEq N P) p0005
  have p0007 :=
    @g_addceq1 (.cv m) (.cv k) N
  have p0008_e00_recanon : Nominal.NPrf (.imp (.objEq m k) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv k) N))) :=
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
      p0007
  have p0008 :=
    @g_neeq1d (.objEq m k) (syn_cplc (.cv m) N) (syn_cplc (.cv k) N) (syn_c0) p0008_e00_recanon
  have p0009 :=
    @g_addceq1 (.cv m) (.cv k) P
  have p0010_e00_recanon : Nominal.NPrf (.imp (.objEq m k) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv k) N))) :=
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
      p0007
  have p0010_e01_recanon : Nominal.NPrf (.imp (.objEq m k) (.classEq (syn_cplc (.cv m) P) (syn_cplc (.cv k) P))) :=
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
      p0009
  have p0010 :=
    @g_eqeq12d (.objEq m k) (syn_cplc (.cv m) N) (syn_cplc (.cv k) N) (syn_cplc (.cv m) P) (syn_cplc (.cv k) P) p0010_e00_recanon p0010_e01_recanon
  have p0011 :=
    @g_anbi12d (.objEq m k) (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)) p0008 p0010
  have p0012 :=
    @g_imbi1d (.objEq m k) (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P))) (.classEq N P) p0011
  have p0013 :=
    @g_addceq1 (.cv m) (syn_cplc (.cv k) (syn_c1c)) N
  have p0014 :=
    @g_addc32 (.cv k) (syn_c1c) N
  have p0015 :=
    @g_syl6eq (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_cplc (.cv m) N) (syn_cplc (syn_cplc (.cv k) (syn_c1c)) N) (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) p0013 p0014
  have p0016 :=
    @g_neeq1d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_cplc (.cv m) N) (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0) p0015
  have p0017 :=
    @g_addceq1 (.cv m) (syn_cplc (.cv k) (syn_c1c)) P
  have p0018 :=
    @g_addc32 (.cv k) (syn_c1c) P
  have p0019 :=
    @g_syl6eq (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_cplc (.cv m) P) (syn_cplc (syn_cplc (.cv k) (syn_c1c)) P) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)) p0017 p0018
  have p0020 :=
    @g_eqeq12d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_cplc (.cv m) N) (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (.cv m) P) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)) p0015 p0019
  have p0021 :=
    @g_anbi12d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))) p0016 p0020
  have p0022 :=
    @g_imbi1d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))) (.classEq N P) p0021
  have p0023 :=
    @g_addceq1 (.cv m) M N
  have p0024 :=
    @g_neeq1d (.classEq (.cv m) M) (syn_cplc (.cv m) N) (syn_cplc M N) (syn_c0) p0023
  have p0025 :=
    @g_addceq1 (.cv m) M P
  have p0026 :=
    @g_eqeq12d (.classEq (.cv m) M) (syn_cplc (.cv m) N) (syn_cplc M N) (syn_cplc (.cv m) P) (syn_cplc M P) p0023 p0025
  have p0027 :=
    @g_anbi12d (.classEq (.cv m) M) (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)) (.classEq (syn_cplc M N) (syn_cplc M P)) p0024 p0026
  have p0028 :=
    @g_imbi1d (.classEq (.cv m) M) (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (syn_wa (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P))) (.classEq N P) p0027
  have p0029 :=
    @g_addcid2 N
  have p0030 :=
    @g_addcid2 P
  have p0031 :=
    @g_eqeq12i (syn_cplc (syn_c0c) N) N (syn_cplc (syn_c0c) P) P p0029 p0030
  have p0032 :=
    @g_biimpi (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P)) (.classEq N P) p0031
  have p0033 :=
    @g_adantl (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P)) (.classEq N P) (syn_wne (syn_cplc (syn_c0c) N) (syn_c0)) p0032
  have p0034 :=
    @g_a1i (.imp (syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0)) (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P))) (.classEq N P)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) p0033
  have p0035 :=
    @g_addcnnul (syn_cplc (.cv k) N) (syn_c1c)
  have p0036 :=
    @g_simpld (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (syn_wne (syn_c1c) (syn_c0)) p0035
  have p0037 :=
    @g_ad2antrl (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))) p0036
  have p0038 :=
    @g_simpll (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))
  have p0039 :=
    @g_simplrl (.classMem (.cv k) (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))
  have p0040 :=
    @g_nncaddccl (.cv k) N
  have p0041 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))) (.classMem (.cv k) (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (syn_cplc (.cv k) N) (syn_cnnc)) p0038 p0039 p0040
  have p0042 :=
    @g_simplrr (.classMem (.cv k) (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))
  have p0043 :=
    @g_nncaddccl (.cv k) P
  have p0044 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))) (.classMem (.cv k) (syn_cnnc)) (.classMem P (syn_cnnc)) (.classMem (syn_cplc (.cv k) P) (syn_cnnc)) p0038 p0042 p0043
  have p0045 :=
    @g_simprr (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))
  have p0046 :=
    @g_simprl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))
  have p0047 :=
    @g_prepeano4 (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)
  have p0048 :=
    @g_syl22anc (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))) (.classMem (syn_cplc (.cv k) N) (syn_cnnc)) (.classMem (syn_cplc (.cv k) P) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)) p0041 p0044 p0045 p0046 p0047
  have p0049 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))) (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)) p0037 p0048
  have p0050 :=
    @g_ex (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))) (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P))) p0049
  have p0051 :=
    @g_imim1d (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))) (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P))) (.classEq N P) p0050
  have p0052 :=
    @g_findsd (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (.classEq N P)) (.imp (syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0)) (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P))) (.classEq N P)) (.imp (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P))) (.classEq N P)) (.imp (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))) (.classEq N P)) (.imp (syn_wa (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P))) (.classEq N P)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) m k M (syn_cvv) (by exact (show m ∉ (M).fv from (by exact fresh_m_not_M))) (by exact (show m ∉ ((Wff.imp (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P))) (.classEq N P))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)))).fv) ∪ (((Wff.classEq N P)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((syn_wne (syn_cplc (.cv k) N) (syn_c0))).fv) ∪ (((Wff.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wne (syn_cplc (.cv k) N) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show m ∉ (((syn_cplc (.cv k) N)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (.cv k) N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv k)).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))) (show m ∉ (N).fv from (by exact fresh_m_not_N)))))) (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((Wff.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ (((syn_cplc (.cv k) N)).fv) ∪ (((syn_cplc (.cv k) P)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (.cv k) N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv k)).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))) (show m ∉ (N).fv from (by exact fresh_m_not_N)))))) (show m ∉ ((syn_cplc (.cv k) P)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv k)).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))) (show m ∉ (P).fv from (by exact fresh_m_not_P)))))))))))))) (show m ∉ ((Wff.classEq N P)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ ((N).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ (N).fv from (by exact fresh_m_not_N)) (show m ∉ (P).fv from (by exact fresh_m_not_P))))))))))) (by exact (show k ∉ ((syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show k ∉ (((Wff.classMem N (syn_cnnc))).fv) ∪ (((Wff.classMem P (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ (N).fv from (by exact fresh_k_not_N)) (show k ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.classMem P (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ ((P).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ (P).fv from (by exact fresh_k_not_P)) (show k ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show k ∉ ((Wff.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (.classEq N P))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)))).fv) ∪ (((Wff.classEq N P)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0)) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show k ∉ (((syn_wne (syn_cplc (.cv m) N) (syn_c0))).fv) ∪ (((Wff.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_wne (syn_cplc (.cv m) N) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show k ∉ (((syn_cplc (.cv m) N)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_cplc (.cv m) N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show k ∉ (((Class.cv m)).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))) (show k ∉ (N).fv from (by exact fresh_k_not_N)))))) (show k ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show k ∉ ((Wff.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show k ∉ (((syn_cplc (.cv m) N)).fv) ∪ (((syn_cplc (.cv m) P)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_cplc (.cv m) N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show k ∉ (((Class.cv m)).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))) (show k ∉ (N).fv from (by exact fresh_k_not_N)))))) (show k ∉ ((syn_cplc (.cv m) P)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show k ∉ (((Class.cv m)).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ m from (by exact fresh_k_ne_m)))))) (show k ∉ (P).fv from (by exact fresh_k_not_P)))))))))))))) (show k ∉ ((Wff.classEq N P)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show k ∉ ((N).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ (N).fv from (by exact fresh_k_not_N)) (show k ∉ (P).fv from (by exact fresh_k_not_P))))))))))) (by exact (show m ∉ ((Wff.imp (syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0)) (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P))) (.classEq N P))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0)) (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P)))).fv) ∪ (((Wff.classEq N P)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0)) (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((syn_wne (syn_cplc (syn_c0c) N) (syn_c0))).fv) ∪ (((Wff.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wne (syn_cplc (syn_c0c) N) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show m ∉ (((syn_cplc (syn_c0c) N)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (syn_c0c) N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((syn_c0c)).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show m ∉ (N).fv from (by exact fresh_m_not_N)))))) (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((Wff.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ (((syn_cplc (syn_c0c) N)).fv) ∪ (((syn_cplc (syn_c0c) P)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (syn_c0c) N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((syn_c0c)).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show m ∉ (N).fv from (by exact fresh_m_not_N)))))) (show m ∉ ((syn_cplc (syn_c0c) P)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((syn_c0c)).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show m ∉ (P).fv from (by exact fresh_m_not_P)))))))))))))) (show m ∉ ((Wff.classEq N P)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ ((N).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ (N).fv from (by exact fresh_m_not_N)) (show m ∉ (P).fv from (by exact fresh_m_not_P))))))))))) (by exact (show m ∉ ((Wff.imp (syn_wa (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P))) (.classEq N P))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P)))).fv) ∪ (((Wff.classEq N P)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((syn_wne (syn_cplc M N) (syn_c0))).fv) ∪ (((Wff.classEq (syn_cplc M N) (syn_cplc M P))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wne (syn_cplc M N) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show m ∉ (((syn_cplc M N)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc M N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ (M).fv from (by exact fresh_m_not_M)) (show m ∉ (N).fv from (by exact fresh_m_not_N)))))) (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((Wff.classEq (syn_cplc M N) (syn_cplc M P))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ (((syn_cplc M N)).fv) ∪ (((syn_cplc M P)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc M N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ (M).fv from (by exact fresh_m_not_M)) (show m ∉ (N).fv from (by exact fresh_m_not_N)))))) (show m ∉ ((syn_cplc M P)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ ((M).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ (M).fv from (by exact fresh_m_not_M)) (show m ∉ (P).fv from (by exact fresh_m_not_P)))))))))))))) (show m ∉ ((Wff.classEq N P)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ ((N).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ (N).fv from (by exact fresh_m_not_N)) (show m ∉ (P).fv from (by exact fresh_m_not_P))))))))))) (by exact (show m ∉ ((Wff.imp (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))) (.classEq N P))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))).fv) ∪ (((Wff.classEq N P)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))).fv) ∪ (((Wff.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show m ∉ (((syn_cplc (syn_cplc (.cv k) N) (syn_c1c))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (syn_cplc (.cv k) N) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((syn_cplc (.cv k) N)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (.cv k) N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv k)).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))) (show m ∉ (N).fv from (by exact fresh_m_not_N)))))) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((Wff.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ (((syn_cplc (syn_cplc (.cv k) N) (syn_c1c))).fv) ∪ (((syn_cplc (syn_cplc (.cv k) P) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (syn_cplc (.cv k) N) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((syn_cplc (.cv k) N)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (.cv k) N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv k)).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))) (show m ∉ (N).fv from (by exact fresh_m_not_N)))))) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((syn_cplc (syn_cplc (.cv k) P) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((syn_cplc (.cv k) P)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (.cv k) P)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv k)).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))) (show m ∉ (P).fv from (by exact fresh_m_not_P)))))) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show m ∉ ((Wff.classEq N P)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ ((N).fv) ∪ ((P).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ (N).fv from (by exact fresh_m_not_N)) (show m ∉ (P).fv from (by exact fresh_m_not_P))))))))))) (show m ≠ k from (by exact fresh_m_ne_k)) p0000 p0006 p0012 p0022 p0028 p0034 p0051
  have p0053 :=
    @g_n_3impb (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)) (.imp (syn_wa (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P))) (.classEq N P)) p0052
  have p0054 :=
    @g_expdimp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P)) (.classEq N P) p0053
  have p0055 :=
    @g_addceq2 N P M
  have p0056 :=
    @g_impbid1 (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wne (syn_cplc M N) (syn_c0))) (.classEq (syn_cplc M N) (syn_cplc M P)) (.classEq N P) p0054 p0055
  exact p0056

noncomputable def g_nulge
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem (syn_c0) (syn_cnnc)) (.classMem A V)) (.classMem (syn_copk A (syn_c0)) (syn_clefin))) := by
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
    @g_addcnul1 A
  have p0001 :=
    @g_eqcomi (syn_cplc A (syn_c0)) (syn_c0) p0000
  have p0002 :=
    @g_addceq2 (.cv x) (syn_c0) A
  have p0003 :=
    @g_eqeq2d (.classEq (.cv x) (syn_c0)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0)) (syn_c0) p0002
  have p0004 :=
    @g_rspcev (.classEq (syn_c0) (syn_cplc A (.cv x))) (.classEq (syn_c0) (syn_cplc A (syn_c0))) x (syn_c0) (syn_cnnc) (by exact (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((Wff.classEq (syn_c0) (syn_cplc A (syn_c0)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_c0)).fv) ∪ (((syn_cplc A (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_cplc A (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0003
  have p0005 :=
    @g_mpan2 (.classMem (syn_c0) (syn_cnnc)) (.classEq (syn_c0) (syn_cplc A (syn_c0))) (syn_wrex x (syn_cnnc) (.classEq (syn_c0) (syn_cplc A (.cv x)))) p0001 p0004
  have p0006 :=
    @g_adantr (.classMem (syn_c0) (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classEq (syn_c0) (syn_cplc A (.cv x)))) (.classMem A V) p0005
  have p0007 :=
    @g_opklefing x A (syn_c0) V (syn_cnnc) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0008 :=
    @g_ancoms (.classMem A V) (.classMem (syn_c0) (syn_cnnc)) (syn_wb (.classMem (syn_copk A (syn_c0)) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq (syn_c0) (syn_cplc A (.cv x))))) p0007
  have p0009 :=
    @g_mpbird (syn_wa (.classMem (syn_c0) (syn_cnnc)) (.classMem A V)) (.classMem (syn_copk A (syn_c0)) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq (syn_c0) (syn_cplc A (.cv x)))) p0006 p0008
  exact p0009

noncomputable def g_ltfinirr
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (.neg (.classMem (syn_copk A A) (syn_cltfin)))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_n_0cnsuc (.cv x)
  have p0001 :=
    @g_necomi (syn_cplc (.cv x) (syn_c1c)) (syn_c0c) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_c0c) (syn_cplc (.cv x) (syn_c1c)))))
  have p0003 :=
    @g_mpbi (syn_wne (syn_c0c) (syn_cplc (.cv x) (syn_c1c))) (.neg (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c)))) p0001 p0002
  have p0004 :=
    @g_addcid1 A
  have p0005 :=
    @g_eqcomi (syn_cplc A (syn_c0c)) A p0004
  have p0006 :=
    @g_addcass A (.cv x) (syn_c1c)
  have p0007 :=
    @g_eqeq12i A (syn_cplc A (syn_c0c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (syn_cplc A (syn_cplc (.cv x) (syn_c1c))) p0005 p0006
  have p0008 :=
    @g_simpll (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)) (.classMem (.cv x) (syn_cnnc))
  have p0009 :=
    @g_peano1
  have p0010 :=
    @g_a1i (.classMem (syn_c0c) (syn_cnnc)) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) p0009
  have p0011 :=
    @g_peano2 (.cv x)
  have p0012 :=
    @g_adantl (.classMem (.cv x) (syn_cnnc)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)) (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0))) p0011
  have p0013 :=
    @g_neeq1i (syn_cplc A (syn_c0c)) A (syn_c0) p0004
  have p0014 :=
    @g_biimpri (syn_wne (syn_cplc A (syn_c0c)) (syn_c0)) (syn_wne A (syn_c0)) p0013
  have p0015 :=
    @g_ad2antlr (syn_wne A (syn_c0)) (syn_wne (syn_cplc A (syn_c0c)) (syn_c0)) (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) p0014
  have p0016 :=
    @g_preaddccan2 (syn_cplc (.cv x) (syn_c1c)) A (syn_c0c)
  have p0017 :=
    @g_syl31anc (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classMem A (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)) (syn_wne (syn_cplc A (syn_c0c)) (syn_c0)) (syn_wb (.classEq (syn_cplc A (syn_c0c)) (syn_cplc A (syn_cplc (.cv x) (syn_c1c)))) (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c)))) p0008 p0010 p0012 p0015 p0016
  have p0018 :=
    @g_syl5bb (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq (syn_cplc A (syn_c0c)) (syn_cplc A (syn_cplc (.cv x) (syn_c1c)))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c))) p0007 p0017
  have p0019 :=
    @g_mtbiri (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c))) p0003 p0018
  have p0020 :=
    @g_nrexdv (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0))) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) x (syn_cnnc) (by exact (show x ∉ ((syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classMem A (syn_cnnc))).fv) ∪ (((syn_wne A (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem A (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((syn_wne A (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show x ∉ ((A).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0019
  have p0021 :=
    @g_ex (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)) (.neg (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) p0020
  have p0022 :=
    @g_imnan (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
  have p0023 :=
    @g_sylib (.classMem A (syn_cnnc)) (.imp (syn_wne A (syn_c0)) (.neg (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))) (.neg (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))) p0021 p0022
  have p0024 :=
    @g_opkltfing x A A (syn_cnnc) (syn_cnnc) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0025 :=
    @g_anidms (.classMem A (syn_cnnc)) (syn_wb (.classMem (syn_copk A A) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))) p0024
  have p0026 :=
    @g_mtbird (.classMem A (syn_cnnc)) (.classMem (syn_copk A A) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) p0023 p0025
  exact p0026



#print axioms g_ltfinirr

end NFChoice.DirectNominalPrf.WPPReplay
