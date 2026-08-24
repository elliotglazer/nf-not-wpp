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
import NominalWPPReplayChunk016Compact001Part020

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

noncomputable def g_wecutisogenfixedfwd
    (x : Var) (y : Var) (D : Class) (R : Class) (S : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_y : y ∉ E.fv) (dv_R_f : f ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_f : f ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y) (hyp_wecutisogenfixedfwd_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisogenfixedfwd_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv f) (syn_cwecutisogen R D S E))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({f} : Finset Var) ∪ E.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_ne_f : r ≠ f := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_r : f ≠ r :=
    Ne.symm fresh_r_ne_f
  have fresh_r_not_E : r ∉ E.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_chnwcutcode R D (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_f_x, dv_D_f, dv_R_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_chnwcutcode R D (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_D, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_chnwcutcode S E (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_f_y, dv_E_f, dv_S_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_chnwcutcode S E (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_y, fresh_r_not_E, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0008 : r ∉ ((Wff.classMem (.cv f) (syn_cwecutisogen R D S E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutisogen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_f, fresh_r_not_D, fresh_r_not_E, fresh_r_not_R, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : r ∉ ((syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_D, fresh_r_ne_y, fresh_r_not_E, fresh_r_not_R, fresh_r_not_S, fresh_r_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0001 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0000 p0001
  have p0003 :=
    @g_wecutisogencodeambient x D R hyp_wecutisogenfixedfwd_1
  have p0004 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv))) p0002 p0003
  have p0005 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0006 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0007 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0005 p0006
  have p0008 :=
    @g_wecutisogencodeambient y E S hyp_wecutisogenfixedfwd_2
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv y) E) (.classMem (syn_chnwcutcode S E (.cv y)) (syn_chwcn (syn_cvv))) p0007 p0008
  have p0010 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv))) (.classMem (syn_chnwcutcode S E (.cv y)) (syn_chwcn (syn_cvv))) p0004 p0009
  have p0011 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0012 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0013 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0014 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0012 p0013
  have p0015 :=
    @g_wecutisogencodeparts x D R hyp_wecutisogenfixedfwd_1
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv x) D) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0014 p0015
  have p0017 :=
    @g_simpl (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0016 p0017
  have p0019 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.cv f)
  have p0020 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))) p0018 p0019
  have p0021 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0022 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0021 p0022
  have p0024 :=
    @g_wecutisogencodeparts y E S hyp_wecutisogenfixedfwd_2
  have p0025 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv y) E) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) p0023 p0024
  have p0026 :=
    @g_simpl (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0027 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) p0025 p0026
  have p0028 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.cv f)
  have p0029 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))) p0027 p0028
  have p0030 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) p0020 p0029
  have p0031 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0032 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0031 p0032
  have p0034 :=
    @g_wecutisogencodeparts x D R hyp_wecutisogenfixedfwd_1
  have p0035 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv x) D) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0033 p0034
  have p0036 :=
    @g_simpr (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0037 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0035 p0036
  have p0038 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.cv f)
  have p0039 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))) p0037 p0038
  have p0040 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) p0030 p0039
  have p0041 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0042 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0043 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0041 p0042
  have p0044 :=
    @g_wecutisogencodeparts y E S hyp_wecutisogenfixedfwd_2
  have p0045 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv y) E) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) p0043 p0044
  have p0046 :=
    @g_simpr (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0047 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) p0045 p0046
  have p0048 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.cv f)
  have p0049 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) p0047 p0048
  have p0050 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) p0040 p0049
  have p0051 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) p0011 p0050
  have p0052 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv))) (.classMem (syn_chnwcutcode S E (.cv y)) (syn_chwcn (syn_cvv)))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y)))) p0010 p0051
  have p0053 :=
    @g_wecutisogenrawcl (syn_cvv) (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode S E (.cv y)) f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0054 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv))) (.classMem (syn_chnwcutcode S E (.cv y)) (syn_chwcn (syn_cvv)))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode S E (.cv y))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode S E (.cv y))))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) p0052 p0053
  have p0055 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
  have p0056 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0057 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0058 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0056 p0057
  have p0059 :=
    @g_wecutisogencodeinran x D R hyp_wecutisogenfixedfwd_1
  have p0060 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D))) p0058 p0059
  have p0061 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0062 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0063 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0061 p0062
  have p0064 :=
    @g_wecutisogencodeinran y E S hyp_wecutisogenfixedfwd_2
  have p0065 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv y) E) (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E))) p0063 p0064
  have p0066 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E))) p0060 p0065
  have p0067 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E)))) p0055 p0066
  have p0068 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
  have p0069 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))) (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) p0067 p0068
  have p0070 :=
    @g_wecutisogenrawmem (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode S E (.cv y)) D R S f E r
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))) (syn_wa (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_chnwcutcode S E (.cv y)) (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))) (.classMem (.cv f) (syn_cwecutisogen R D S E)) p0069 p0070
  have p0072 :=
    @g_rexlimddv (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (.classMem (.cv f) (syn_cwecutisogen R D S E)) r (syn_cvv) dv_cache_0008 dv_cache_0009 p0054 p0071
  exact p0072

#print axioms g_wecutisogenfixedfwd

end NFChoice.DirectNominalPrf.WPPReplay
