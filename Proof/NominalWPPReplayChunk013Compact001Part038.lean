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
import NominalAlphaRepairedBase001038Leaf1stReflected001
import NominalAlphaRepairedBase001039SwapReflected001
import NominalAlphaRepairedBase001040SsetReflected001
import NominalAlphaRepairedBase001041CoReflected001
import NominalAlphaRepairedBase001042ImaReflected001
import NominalAlphaRepairedBase001043SiReflected001
import NominalAlphaRepairedBase001044IdReflected001
import NominalAlphaRepairedBase001045XpReflected001
import NominalAlphaRepairedBase001046CnvReflected001
import NominalAlphaRepairedBase001047FvReflected001
import NominalAlphaRepairedBase001048Leaf2ndReflected001
import NominalAlphaRepairedBase001049OprabReflected001
import NominalAlphaPrefix050WppNotmem014Data
import NominalAlphaGlobal051ProofData001
import NominalAlphaRelease004Coarse052
import NominalAlphaRelease004Coarse053
import NominalAlphaRelease004Coarse054
import NominalAlphaRelease004Coarse055
import NominalAlphaRelease004Coarse056
import NominalAlphaRelease004Coarse057
import NominalAlphaRelease004Coarse058
import NominalAlphaRelease004Coarse059
import NominalAlphaRelease004Coarse060
import NominalAlphaRelease004Coarse061
import NominalAlphaRelease004Coarse062
import NominalAlphaRelease004Coarse063
import NominalAlphaRelease004Coarse064
import NominalAlphaRelease004Coarse065
import NominalAlphaRelease004Coarse066
import NominalAlphaRelease004Coarse067
import NominalAlphaRelease004Coarse068
import NominalAlphaRelease004Coarse069
import NominalAlphaRelease004Coarse070
import NominalAlphaRelease004Coarse071
import NominalAlphaRelease004Coarse072
import NominalAlphaRelease004Coarse073
import NominalAlphaRelease004Coarse074
import NominalAlphaRelease004Coarse075
import NominalAlphaRelease004Coarse076
import NominalAlphaRelease004Coarse077
import NominalAlphaRelease004Coarse078
import NominalAlphaRelease004Coarse079
import NominalAlphaRelease004Coarse080
import NominalAlphaRelease004Coarse081
import NominalAlphaRelease004Coarse082
import NominalAlphaRelease004Coarse083
import NominalAlphaRelease004Coarse084
import NominalAlphaRelease004Coarse085
import NominalAlphaRelease004Coarse086
import NominalAlphaRelease004Coarse087
import NominalAlphaHygieneV5Probe088
import NominalAlphaRelease004Coarse089
import NominalAlphaRelease004Coarse090
import NominalAlphaHygieneV5Coalesced091B
import NominalAlphaHygieneV5Coalesced092
import NominalAlphaHygieneV5Coalesced093
import NominalAlphaHygieneV5Coalesced094
import NominalAlphaHygieneV5Coalesced095
import NominalAlphaHygieneV5Coalesced096
import NominalAlphaHygieneV5Coalesced097
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk013Compact001Part037

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

noncomputable def g_enprmaplem1
    (x : Var) (A : Class) (B : Class) (W : Class) (r : Var) (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (dv_r_x : r ≠ x) (hyp_enprmaplem1_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))))) :
    Nominal.NPrf (.classMem W (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ W.fv ∪ ({r} : Finset Var)
  let y : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_W : t ∉ W.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_ne_r : t ≠ r := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_t : r ≠ t :=
    Ne.symm fresh_t_ne_r
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have dv_cache_0001 : t ∉ ((syn_cop (syn_csn (.cv y)) (.cv r))).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_cop (.cv y) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ ((Wff.classMem (syn_cop (.cv y) (.cv x)) (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, fresh_t_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((syn_co A (syn_cmap) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, dv_B_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_cima (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_r_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cima (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have p0000 :=
    @g_elima1c t (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_oteltxp (syn_csn (.cv t)) (syn_csn (.cv y)) (.cv r) (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)
  have p0002 :=
    @g_vex t
  have p0003 :=
    @g_vex y
  have p0004 :=
    @g_opsnelsi (.cv t) (.cv y) (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) p0002 p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv t) (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) (.cv y))))
  have p0006 :=
    @g_brres (.cv t) (.cv y) (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))
  have p0007 :=
    @g_eliniseg (syn_c2nd) (.cv x) (.cv t)
  have p0008 :=
    @g_anbi2i (.classMem (.cv t) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) (syn_wbr (.cv t) (syn_c2nd) (.cv x)) (syn_wbr (.cv t) (syn_c1st) (.cv y)) p0007
  have p0009 :=
    @g_bitri (syn_wbr (.cv t) (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) (.cv y)) (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv y)) (.classMem (.cv t) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv y)) (syn_wbr (.cv t) (syn_c2nd) (.cv x))) p0006 p0008
  have p0010 :=
    @g_bitr3i (.classMem (syn_cop (.cv t) (.cv y)) (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_wbr (.cv t) (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) (.cv y)) (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv y)) (syn_wbr (.cv t) (syn_c2nd) (.cv x))) p0005 p0009
  have p0011 :=
    @g_vex x
  have p0012 :=
    @g_op1st2nd (.cv y) (.cv x) (.cv t) p0003 p0011
  have p0013 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (.cv y))) (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))) (.classMem (syn_cop (.cv t) (.cv y)) (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv y)) (syn_wbr (.cv t) (syn_c2nd) (.cv x))) (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) p0004 p0010 p0012
  have p0014 :=
    @g_vex r
  have p0015 :=
    @g_opelssetsn (.cv t) (.cv r) p0002 p0014
  have p0016_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset)) (.objMem t r)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0015
  have p0016 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (.cv y))) (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))) (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset)) (.objMem t r) p0013 p0016_e01_recanon
  have p0017 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (.cv r))) (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset))) (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (.cv y))) (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))) (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset))) (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r)) p0001 p0016
  have p0018 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (.cv r))) (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset))) (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r)) t p0017
  have p0019 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_cima (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c))) (syn_wex t (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (.cv r))) (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)))) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r))) p0000 p0018
  have p0020 :=
    @g_opex (.cv y) (.cv x) p0003 p0011
  have p0021 :=
    @g_eleq1 (.cv t) (syn_cop (.cv y) (.cv x)) (.cv r)
  have p0022_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (syn_wb (.objMem t r) (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0021
  have p0022 :=
    @g_ceqsexv (.objMem t r) (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) t (syn_cop (.cv y) (.cv x)) dv_cache_0003 dv_cache_0004 p0020 p0022_e01_recanon
  have p0023 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv x))))
  have p0024 :=
    @g_bitr4i (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r))) (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) (syn_wbr (.cv y) (.cv r) (.cv x)) p0022 p0023
  have p0025 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_cima (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c))) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r))) (syn_wbr (.cv y) (.cv r) (.cv x)) p0019 p0024
  have p0026 :=
    @g_eliniseg (.cv r) (.cv x) (.cv y)
  have p0027 :=
    @g_bitr4i (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_cima (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c))) (syn_wbr (.cv y) (.cv r) (.cv x)) (.classMem (.cv y) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) p0025 p0026
  have p0028 :=
    @g_releqmpt r y (syn_co A (syn_cmap) B) (syn_cima (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c)) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0027
  have p0029 :=
    @g_eqtr4i W (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) (syn_cin (syn_cxp (syn_co A (syn_cmap) B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c)))) (syn_c1c))))) hyp_enprmaplem1_1 p0028
  have p0030 :=
    @g_ovex A B (syn_cmap)
  have p0031 :=
    @g_n_1stex
  have p0032 :=
    @g_n_2ndex
  have p0033 :=
    @g_cnvex (syn_c2nd) p0032
  have p0034 :=
    @g_snex (.cv x)
  have p0035 :=
    @g_imaex (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)) p0033 p0034
  have p0036 :=
    @g_resex (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))) p0031 p0035
  have p0037 :=
    @g_siex (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) p0036
  have p0038 :=
    @g_ssetex
  have p0039 :=
    @g_txpex (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset) p0037 p0038
  have p0040 :=
    @g_n_1cex
  have p0041 :=
    @g_imaex (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c) p0039 p0040
  have p0042 :=
    @g_mptexlem (syn_co A (syn_cmap) B) (syn_cima (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c)) p0030 p0041
  have p0043 :=
    @g_eqeltri W (syn_cin (syn_cxp (syn_co A (syn_cmap) B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_ctxp (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset)) (syn_c1c)))) (syn_c1c))))) (syn_cvv) p0029 p0042
  exact p0043

noncomputable def g_enprmaplem2
    (x : Var) (A : Class) (B : Class) (W : Class) (r : Var) (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (hyp_enprmaplem2_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))))) :
    Nominal.NPrf (syn_wfn W (syn_co A (syn_cmap) B)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ W.fv ∪ ({r} : Finset Var)
  have dv_cache_0001 : r ∉ ((syn_co A (syn_cmap) B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, dv_B_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fnmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) W (syn_cvv) dv_cache_0001 hyp_enprmaplem2_1
  have p0001 :=
    @g_vex r
  have p0002 :=
    @g_cnvex (.cv r) p0001
  have p0003 :=
    @g_snex (.cv x)
  have p0004 :=
    @g_imaex (syn_ccnv (.cv r)) (syn_csn (.cv x)) p0002 p0003
  have p0005 :=
    @g_a1i (.classMem (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cvv)) (.classMem (.cv r) (syn_co A (syn_cmap) B)) p0004
  have p0006 :=
    @g_mprg (.classMem (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cvv)) (syn_wfn W (syn_co A (syn_cmap) B)) r (syn_co A (syn_cmap) B) p0000 p0005
  exact p0006

#print axioms g_enprmaplem2

end NFChoice.DirectNominalPrf.WPPReplay
