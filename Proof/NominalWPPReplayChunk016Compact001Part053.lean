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
import NominalWPPReplayChunk016Compact001Part052

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

noncomputable def g_hncodetrncndndv
    (u : Var) (D : Class) (E : Class) (F : Class) (hyp_hncodetrncndndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hncodetrncndndv_2 : Nominal.NPrf (syn_wf1o F D E)) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ D.fv ∪ E.fv ∪ F.fv
  let r : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let f : Var := freshVar proofSupport 3
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_u : r ≠ u := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_r : u ≠ r :=
    Ne.symm fresh_r_ne_u
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_E : r ∉ E.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_f_ne_u : f ≠ u := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_f : u ≠ f :=
    Ne.symm fresh_f_ne_u
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_r_ne_y : r ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_r_ne_x : r ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_f : r ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_f_ne_r : f ≠ r :=
    Ne.symm fresh_r_ne_f
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_f : y ≠ f := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_x_ne_f : x ≠ f := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have dv_cache_0001 : f ≠ r := by
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0002 : f ≠ x := by
    clear dv_cache_0001
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0003 : f ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0004 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0005 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : f ∉ ((syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, fresh_f_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : f ∉ ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_not_F, fresh_f_ne_u, fresh_f_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : r ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : r ∉ ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : f ∉ ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_not_F, fresh_f_ne_u, fresh_f_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : r ∉ ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex u
  have p0001 :=
    @g_hncodetrnfnvalndv u F hyp_hncodetrncndndv_1 p0000
  have p0002 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u)))))
  have p0003 :=
    @g_cnvcnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0004 :=
    @g_coeq1i (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0003
  have p0005 :=
    @g_coeq1i (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0004
  have p0006 :=
    @g_eqtri (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0002 p0005
  have p0007 :=
    @g_hwcnpair u D
  have p0008 :=
    @g_id (.classMem (.cv u) (syn_chwcn D))
  have p0009 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0007 p0008
  have p0010 :=
    @g_vex u
  have p0011 :=
    @g_elhwcncl D (.cv u)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0012
  have p0014 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))) (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0013 p0008
  have p0015 :=
    @g_simpl (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
  have p0016 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcodes D)) p0014 p0015
  have p0017 :=
    @g_eqeltrrd (.classMem (.cv u) (syn_chwcn D)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D) p0009 p0016
  have p0018 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0019 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0020 :=
    @g_elhwcodesclndv (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) D p0018 p0019
  have p0021 :=
    @g_sylib (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) p0017 p0020
  have p0022 :=
    @g_simpr (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
  have p0023 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) p0021 p0022
  have p0024 :=
    @g_f1of1 D E F
  have p0025 :=
    Nominal.mp hyp_hncodetrncndndv_2 p0024
  have p0026 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) (syn_wf1 F D E) p0023 p0025
  have p0027 :=
    @g_f1ores D E (syn_cfv (syn_c2nd) (.cv u)) F
  have p0028 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wf1 F D E) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) p0026 p0027
  have p0029 :=
    @g_f1odm (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0030 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u))) p0028 p0029
  have p0031 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u)) p0030
  have p0032 :=
    @g_f1ofo (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0033 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (syn_wfo (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) p0028 p0032
  have p0034 :=
    @g_forn (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0035 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wfo (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) p0033 p0034
  have p0036 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D)) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) p0035
  have p0037 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0031 p0036
  have p0038 :=
    @g_f1oeq23 (syn_cfv (syn_c2nd) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0039 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0037 p0038
  have p0040 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0028 p0039
  have p0041 :=
    @g_f1ocnv (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0042 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0040 p0041
  have p0043 :=
    @g_simpl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
  have p0044 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0021 p0043
  have p0045 :=
    @g_breq2d (.classMem (.cv u) (syn_chwcn D)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) p0030
  have p0046 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0044 p0045
  have p0047 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0042 p0046
  have p0048 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0049 :=
    @g_biid (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0050 :=
    @g_a1i (syn_wb (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0049
  have p0051 :=
    @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0052 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r) (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0051
  have p0053 :=
    @g_anbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0050 p0052
  have p0054 :=
    @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0055 :=
    @g_coeq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r) (syn_cfv (syn_c1st) (.cv u)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0054
  have p0056 :=
    @g_coeq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0055
  have p0057 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))))
  have p0058 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0057
  have p0059 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u)))))
  have p0060 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0059
  have p0061 :=
    @g_n_3eqtr3g (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) p0056 p0058 p0060
  have p0062 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0061
  have p0063 :=
    @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0053 p0062
  have p0064 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0065 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0064
  have p0066 :=
    @g_dmex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0065
  have p0067 :=
    @g_f1oeq3 (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0068 :=
    @g_id (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0069 :=
    @g_breq2d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r) (syn_cwe) p0068
  have p0070 :=
    @g_anbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0067 p0069
  have p0071 :=
    @g_biid (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0072 :=
    @g_a1i (syn_wb (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0071
  have p0073 :=
    @g_imbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0070 p0072
  have p0074 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0075 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0074
  have p0076 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0075
  have p0077 :=
    @g_f1oeq2 (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0078 :=
    @g_biid (syn_wbr (.cv r) (syn_cwe) (.cv y))
  have p0079 :=
    @g_a1i (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0078
  have p0080 :=
    @g_anbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0077 p0079
  have p0081 :=
    @g_id (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0082 :=
    @g_breq2d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) p0081
  have p0083 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x)) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0080 p0082
  have p0084 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0085 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0084
  have p0086 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0085
  have p0087 :=
    @g_f1oeq1 (.cv x) (.cv y) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0088 :=
    @g_biid (syn_wbr (.cv r) (syn_cwe) (.cv y))
  have p0089 :=
    @g_a1i (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0088
  have p0090 :=
    @g_anbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0087 p0089
  have p0091 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0092 :=
    @g_cnveqd (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0091
  have p0093 :=
    @g_coeq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccnv (.cv f)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r) p0092
  have p0094 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0095 :=
    @g_coeq12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0093 p0094
  have p0096 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r))))
  have p0097 :=
    @g_eqcomi (syn_cpwpull (.cv f) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0096
  have p0098 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))))
  have p0099 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0098
  have p0100 :=
    @g_n_3eqtr3g (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (.cv f) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0095 p0097 p0099
  have p0101 :=
    @g_breq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (.cv f) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (.cv x) (syn_cwe) p0100
  have p0102 :=
    @g_imbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x)) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x)) p0090 p0101
  have p0103 :=
    @g_pwpullwesetimpndv x y f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0104 :=
    @g_vtocl (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x))) (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x))) f (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0007 dv_cache_0008 p0086 p0102 p0103
  have p0105 :=
    @g_vtocl (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x))) (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) x (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0009 dv_cache_0010 p0076 p0083 p0104
  have p0106 :=
    @g_vtocl (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) y (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0011 dv_cache_0012 p0066 p0073 p0105
  have p0107 :=
    @g_vtocl (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) r (syn_cfv (syn_c1st) (.cv u)) dv_cache_0013 dv_cache_0014 p0048 p0063 p0106
  have p0108 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0047 p0107
  have p0109 :=
    @g_syl5eqbrr (.classMem (.cv u) (syn_chwcn D)) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0006 p0108
  have p0110 :=
    @g_imassrn F (syn_cfv (syn_c2nd) (.cv u))
  have p0111 :=
    @g_f1ofo D E F
  have p0112 :=
    Nominal.mp hyp_hncodetrncndndv_2 p0111
  have p0113 :=
    @g_forn D E F
  have p0114 :=
    Nominal.mp p0112 p0113
  have p0115 :=
    @g_sseqtri (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn F) E p0110 p0114
  have p0116 :=
    @g_syl6eqss (.classMem (.cv u) (syn_chwcn D)) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) E p0035 p0115
  have p0117 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E) p0109 p0116
  have p0118 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0119 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0118
  have p0120 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0121 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0119 p0120
  have p0122 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0123 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0122
  have p0124 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0123
  have p0125 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0121 p0124
  have p0126 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0127 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0126
  have p0128 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0127
  have p0129 :=
    @g_elhwcodesclndv (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E p0125 p0128
  have p0130 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wbr (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E)) (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E)) p0117 p0129
  have p0131 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u)))))
  have p0132 :=
    @g_cnvcnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0133 :=
    @g_coeq1i (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0132
  have p0134 :=
    @g_coeq1i (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0133
  have p0135 :=
    @g_eqtri (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0131 p0134
  have p0136 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0135
  have p0137 :=
    @g_f1ofo (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0138 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0042 p0137
  have p0139 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0140 :=
    @g_biid (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0141 :=
    @g_a1i (syn_wb (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0140
  have p0142 :=
    @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0143 :=
    @g_coeq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r) (syn_cfv (syn_c1st) (.cv u)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0142
  have p0144 :=
    @g_coeq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0143
  have p0145 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))))
  have p0146 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0145
  have p0147 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u)))))
  have p0148 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0147
  have p0149 :=
    @g_n_3eqtr3g (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) p0144 p0146 p0148
  have p0150 :=
    @g_sseq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0149
  have p0151 :=
    @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0141 p0150
  have p0152 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0153 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0152
  have p0154 :=
    @g_dmex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0153
  have p0155 :=
    @g_foeq3 (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0156 :=
    @g_biid (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
  have p0157 :=
    @g_a1i (syn_wb (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0156
  have p0158 :=
    @g_imbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0155 p0157
  have p0159 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0160 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0159
  have p0161 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0160
  have p0162 :=
    @g_foeq2 (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0163 :=
    @g_id (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0164 :=
    @g_id (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0165 :=
    @g_xpeq12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0163 p0164
  have p0166 :=
    @g_sseq2d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (.cv x) (.cv x)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0165
  have p0167 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0162 p0166
  have p0168 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0169 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0168
  have p0170 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0169
  have p0171 :=
    @g_foeq1 (.cv x) (.cv y) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0172 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0173 :=
    @g_cnveqd (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0172
  have p0174 :=
    @g_coeq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccnv (.cv f)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r) p0173
  have p0175 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0176 :=
    @g_coeq12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0174 p0175
  have p0177 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r))))
  have p0178 :=
    @g_eqcomi (syn_cpwpull (.cv f) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0177
  have p0179 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))))
  have p0180 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0179
  have p0181 :=
    @g_n_3eqtr3g (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (.cv f) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0176 p0178 p0180
  have p0182 :=
    @g_sseq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (.cv f) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x)) p0181
  have p0183 :=
    @g_imbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x))) p0171 p0182
  have p0184 :=
    @g_pwpullssxpsetimpndv x y f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0185 :=
    @g_vtocl (.imp (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x)))) (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x)))) f (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0007 dv_cache_0015 p0170 p0183 p0184
  have p0186 :=
    @g_vtocl (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x)))) (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) x (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0009 dv_cache_0016 p0161 p0167 p0185
  have p0187 :=
    @g_vtocl (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) y (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0011 dv_cache_0017 p0154 p0158 p0186
  have p0188 :=
    @g_vtocl (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) r (syn_cfv (syn_c1st) (.cv u)) dv_cache_0013 dv_cache_0018 p0139 p0151 p0187
  have p0189 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0138 p0188
  have p0190 :=
    @g_syl5eqss (.classMem (.cv u) (syn_chwcn D)) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0136 p0189
  have p0191 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0192 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0191
  have p0193 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0194 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0192 p0193
  have p0195 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0196 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0195
  have p0197 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0196
  have p0198 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0194 p0197
  have p0199 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0200 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0199
  have p0201 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0200
  have p0202 :=
    @g_opfv1st (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0198 p0201
  have p0203 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0204 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0203
  have p0205 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0206 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0204 p0205
  have p0207 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0208 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0207
  have p0209 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0208
  have p0210 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0206 p0209
  have p0211 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0212 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0211
  have p0213 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0212
  have p0214 :=
    @g_opfv2nd (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0210 p0213
  have p0215 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0216 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0215
  have p0217 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0218 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0216 p0217
  have p0219 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0220 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0219
  have p0221 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0220
  have p0222 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0218 p0221
  have p0223 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0224 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0223
  have p0225 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0224
  have p0226 :=
    @g_opfv2nd (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0222 p0225
  have p0227 :=
    @g_xpeq12i (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0214 p0226
  have p0228 :=
    @g_sseq12i (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0202 p0227
  have p0229 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wss (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))) p0190 p0228
  have p0230 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))) p0130 p0229
  have p0231 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0232 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0231
  have p0233 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0234 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0232 p0233
  have p0235 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0236 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0235
  have p0237 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0236
  have p0238 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0234 p0237
  have p0239 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0240 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0239
  have p0241 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0240
  have p0242 :=
    @g_opex (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0238 p0241
  have p0243 :=
    @g_elhwcncl E (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0244 :=
    Nominal.mp p0242 p0243
  have p0245 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))))) (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcn E)) p0230 p0244
  have p0246 :=
    @g_syl5eqel (.classMem (.cv u) (syn_chwcn D)) (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcn E) p0001 p0245
  exact p0246

#print axioms g_hncodetrncndndv

end NFChoice.DirectNominalPrf.WPPReplay
