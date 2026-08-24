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
import NominalWPPReplayChunk016Compact001Part053

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

noncomputable def g_hnqinctrnvaldndv
    (u : Var) (A : Class) (D : Class) (E : Class) (F : Class) (hyp_hnqinctrnvaldndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hnqinctrnvaldndv_2 : Nominal.NPrf (syn_wf1o F D E)) (hyp_hnqinctrnvaldndv_3 : Nominal.NPrf (syn_wss D A)) (hyp_hnqinctrnvaldndv_4 : Nominal.NPrf (syn_wss E A)) (hyp_hnqinctrnvaldndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (syn_cfv (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ D.fv ∪ E.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
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
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_ne_u : f ≠ u := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_f : u ≠ f :=
    Ne.symm fresh_f_ne_u
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_ne_u : r ≠ u := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_r : u ≠ r :=
    Ne.symm fresh_r_ne_u
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
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
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_F : v ∉ F.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_x_ne_f : x ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_ne_r : x ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_v : x ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_f_ne_r : f ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_f : r ≠ f :=
    Ne.symm fresh_f_ne_r
  have fresh_f_ne_y : f ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_f : y ≠ f :=
    Ne.symm fresh_f_ne_y
  have fresh_f_ne_v : f ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_v_ne_f : v ≠ f :=
    Ne.symm fresh_f_ne_v
  have fresh_r_ne_y : r ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_r_ne_v : r ≠ v := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_v_ne_r : v ≠ r :=
    Ne.symm fresh_r_ne_v
  have fresh_y_ne_v : y ≠ v := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have dv_cache_0001 : x ∉ ((syn_csn (.cv u))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (syn_csn (.cv u))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_D, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cec (.cv u) (syn_chwniso D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cec (.cv u) (syn_chwniso A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_chnqmap1 A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_ccnv (syn_chnqmap1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0008 : f ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0009 : f ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0010 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0011 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : f ∉ ((syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, fresh_f_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : f ∉ ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_not_F, fresh_f_ne_u, fresh_f_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : r ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : r ∉ ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : f ∉ ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_not_F, fresh_f_ne_u, fresh_f_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : r ∉ ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : r ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : r ∉ ((Wff.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : r ∉ ((Wff.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_f, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : f ∉ ((syn_cres F (syn_cfv (syn_c2nd) (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, fresh_f_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : f ∉ ((syn_chwbij)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : f ∉ ((syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, fresh_f_ne_u, fresh_f_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : f ∉ ((Wff.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_v, fresh_f_ne_u, fresh_f_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : r ∉ ((Wff.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_v, fresh_r_ne_u, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : f ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0035 : f ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show f ≠ v from (by exact fresh_f_ne_v))
  have dv_cache_0036 : r ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show r ≠ u from (by exact fresh_r_ne_u))
  have dv_cache_0037 : r ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (show r ≠ v from (by exact fresh_r_ne_v))
  have dv_cache_0038 : v ∉ ((syn_cfv (syn_chncodetrnfn F) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : v ∉ ((syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_F, fresh_v_ne_f, fresh_v_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : x ∉ ((syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0041 : x ∉ ((syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_F, fresh_x_not_E, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0042 : x ∉ ((syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_F, fresh_x_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0043 : x ∉ ((syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_F, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0044 : x ∉ ((syn_ccnv (syn_chnqmap1 E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_f1odm D E F
  have p0001 :=
    Nominal.mp hyp_hnqinctrnvaldndv_2 p0000
  have p0002 :=
    @g_dmex F hyp_hnqinctrnvaldndv_1
  have p0003 :=
    @g_eqeltrri (syn_cdm F) D (syn_cvv) p0001 p0002
  have p0004 :=
    @g_hnqmap1valcl D (.cv u) p0003
  have p0005 :=
    @g_id (.classMem (.cv u) (syn_chwcn D))
  have p0006 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso D)))) (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0004 p0005
  have p0007 :=
    @g_snelpw1 (.cv u) (syn_chwcn D)
  have p0008 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn D))) p0005 p0007
  have p0009 :=
    @g_hnqmap1fn D p0003
  have p0010 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn D))) (syn_wfn (syn_chnqmap1 D) (syn_cpw1 (syn_chwcn D))) p0008 p0009
  have p0011 :=
    @g_fnbrfvb (syn_cpw1 (syn_chwcn D)) (syn_csn (.cv u)) (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqmap1 D)
  have p0012 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wfn (syn_chnqmap1 D) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn D)))) (syn_wb (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso D))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 D) (syn_cec (.cv u) (syn_chwniso D)))) p0010 p0011
  have p0013 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso D))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 D) (syn_cec (.cv u) (syn_chwniso D))) p0006 p0012
  have p0014 :=
    @g_brcnv (syn_cec (.cv u) (syn_chwniso D)) (syn_csn (.cv u)) (syn_chnqmap1 D)
  have p0015 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 D) (syn_cec (.cv u) (syn_chwniso D))) (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (syn_csn (.cv u))) p0013 p0014
  have p0016 :=
    @g_hwcnssbase A D hyp_hnqinctrnvaldndv_3
  have p0017 :=
    @g_ssel (syn_chwcn D) (syn_chwcn A) (.cv u)
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn A))) (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0018 p0005
  have p0020 :=
    @g_hnqmap1valcl A (.cv u) hyp_hnqinctrnvaldndv_5
  have p0021 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A))) p0019 p0020
  have p0022 :=
    @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0023 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0019 p0022
  have p0024 :=
    @g_hnqmap1fn A hyp_hnqinctrnvaldndv_5
  have p0025 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) p0023 p0024
  have p0026 :=
    @g_fnbrfvb (syn_cpw1 (syn_chwcn A)) (syn_csn (.cv u)) (syn_cec (.cv u) (syn_chwniso A)) (syn_chnqmap1 A)
  have p0027 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))) (syn_wb (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A)))) p0025 p0026
  have p0028 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))) p0021 p0027
  have p0029 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (syn_csn (.cv u))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))) p0015 p0028
  have p0030 :=
    @g_snex (.cv u)
  have p0031 :=
    @g_id (.classEq (.cv x) (syn_csn (.cv u)))
  have p0032 :=
    @g_breq2d (.classEq (.cv x) (syn_csn (.cv u))) (.cv x) (syn_csn (.cv u)) (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) p0031
  have p0033 :=
    @g_id (.classEq (.cv x) (syn_csn (.cv u)))
  have p0034 :=
    @g_breq1d (.classEq (.cv x) (syn_csn (.cv u))) (.cv x) (syn_csn (.cv u)) (syn_cec (.cv u) (syn_chwniso A)) (syn_chnqmap1 A) p0033
  have p0035 :=
    @g_anbi12d (.classEq (.cv x) (syn_csn (.cv u))) (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (.cv x)) (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (syn_csn (.cv u))) (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))) p0032 p0034
  have p0036 :=
    @g_spcev (syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (.cv x)) (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A)))) (syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (syn_csn (.cv u))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A)))) x (syn_csn (.cv u)) dv_cache_0001 dv_cache_0002 p0030 p0035
  have p0037 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (syn_csn (.cv u))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A)))) (syn_wex x (syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (.cv x)) (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))))) p0029 p0036
  have p0038 :=
    @g_brco x (syn_cec (.cv u) (syn_chwniso D)) (syn_cec (.cv u) (syn_chwniso A)) (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0039 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wex x (syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (.cv x)) (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cec (.cv u) (syn_chwniso A))) p0037 p0038
  have p0040 :=
    (by simpa [syn_chnqinc] using (Nominal.classEqRefl (syn_chnqinc D A)))
  have p0041 :=
    @g_breqi (syn_cec (.cv u) (syn_chwniso D)) (syn_cec (.cv u) (syn_chwniso A)) (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) p0040
  have p0042 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso A))) p0039 p0041
  have p0043 :=
    @g_hwnisoclasselhnordcl D (.cv u) p0003
  have p0044 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cec (.cv u) (syn_chwniso D)) (syn_chnord D))) (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0043 p0005
  have p0045 :=
    @g_hnqincfn A D hyp_hnqinctrnvaldndv_3 p0003 hyp_hnqinctrnvaldndv_5
  have p0046 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cec (.cv u) (syn_chwniso D)) (syn_chnord D)) (syn_wfn (syn_chnqinc D A) (syn_chnord D)) p0044 p0045
  have p0047 :=
    @g_fnbrfvb (syn_chnord D) (syn_cec (.cv u) (syn_chwniso D)) (syn_cec (.cv u) (syn_chwniso A)) (syn_chnqinc D A)
  have p0048 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (.classMem (syn_cec (.cv u) (syn_chwniso D)) (syn_chnord D))) (syn_wb (.classEq (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso A)))) p0046 p0047
  have p0049 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso A))) p0042 p0048
  have p0050 :=
    @g_ssv D
  have p0051 :=
    @g_hwcnssbase (syn_cvv) D p0050
  have p0052 :=
    @g_ssel (syn_chwcn D) (syn_chwcn (syn_cvv)) (.cv u)
  have p0053 :=
    Nominal.mp p0051 p0052
  have p0054 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn (syn_cvv)))) (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0053 p0005
  have p0055 :=
    @g_vex u
  have p0056 :=
    @g_hncodetrnfnvalndv u F hyp_hnqinctrnvaldndv_1 p0055
  have p0057 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u)))))
  have p0058 :=
    @g_cnvcnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0059 :=
    @g_coeq1i (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0058
  have p0060 :=
    @g_coeq1i (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0059
  have p0061 :=
    @g_eqtri (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0057 p0060
  have p0062 :=
    @g_hwcnpair u D
  have p0063 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0062 p0005
  have p0064 :=
    @g_vex u
  have p0065 :=
    @g_elhwcncl D (.cv u)
  have p0066 :=
    Nominal.mp p0064 p0065
  have p0067 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0066
  have p0068 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))) (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0067 p0005
  have p0069 :=
    @g_simpl (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
  have p0070 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcodes D)) p0068 p0069
  have p0071 :=
    @g_eqeltrrd (.classMem (.cv u) (syn_chwcn D)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D) p0063 p0070
  have p0072 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0073 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0074 :=
    @g_elhwcodesclndv (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) D p0072 p0073
  have p0075 :=
    @g_sylib (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) p0071 p0074
  have p0076 :=
    @g_simpr (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
  have p0077 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) p0075 p0076
  have p0078 :=
    @g_f1of1 D E F
  have p0079 :=
    Nominal.mp hyp_hnqinctrnvaldndv_2 p0078
  have p0080 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) (syn_wf1 F D E) p0077 p0079
  have p0081 :=
    @g_f1ores D E (syn_cfv (syn_c2nd) (.cv u)) F
  have p0082 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wf1 F D E) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) p0080 p0081
  have p0083 :=
    @g_f1odm (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0084 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u))) p0082 p0083
  have p0085 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u)) p0084
  have p0086 :=
    @g_f1ofo (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0087 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (syn_wfo (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) p0082 p0086
  have p0088 :=
    @g_forn (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0089 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wfo (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) p0087 p0088
  have p0090 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D)) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) p0089
  have p0091 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0085 p0090
  have p0092 :=
    @g_f1oeq23 (syn_cfv (syn_c2nd) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0093 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0091 p0092
  have p0094 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0082 p0093
  have p0095 :=
    @g_f1ocnv (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0096 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0094 p0095
  have p0097 :=
    @g_simpl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
  have p0098 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0075 p0097
  have p0099 :=
    @g_breq2d (.classMem (.cv u) (syn_chwcn D)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) p0084
  have p0100 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0098 p0099
  have p0101 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0096 p0100
  have p0102 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0103 :=
    @g_biid (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0104 :=
    @g_a1i (syn_wb (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0103
  have p0105 :=
    @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0106 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r) (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0105
  have p0107 :=
    @g_anbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0104 p0106
  have p0108 :=
    @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0109 :=
    @g_coeq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r) (syn_cfv (syn_c1st) (.cv u)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0108
  have p0110 :=
    @g_coeq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0109
  have p0111 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))))
  have p0112 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0111
  have p0113 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u)))))
  have p0114 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0113
  have p0115 :=
    @g_n_3eqtr3g (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) p0110 p0112 p0114
  have p0116 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0115
  have p0117 :=
    @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0107 p0116
  have p0118 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0119 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0118
  have p0120 :=
    @g_dmex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0119
  have p0121 :=
    @g_f1oeq3 (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0122 :=
    @g_id (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0123 :=
    @g_breq2d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r) (syn_cwe) p0122
  have p0124 :=
    @g_anbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0121 p0123
  have p0125 :=
    @g_biid (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0126 :=
    @g_a1i (syn_wb (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0125
  have p0127 :=
    @g_imbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0124 p0126
  have p0128 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0129 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0128
  have p0130 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0129
  have p0131 :=
    @g_f1oeq2 (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0132 :=
    @g_biid (syn_wbr (.cv r) (syn_cwe) (.cv y))
  have p0133 :=
    @g_a1i (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0132
  have p0134 :=
    @g_anbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0131 p0133
  have p0135 :=
    @g_id (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0136 :=
    @g_breq2d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) p0135
  have p0137 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x)) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0134 p0136
  have p0138 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0139 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0138
  have p0140 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0139
  have p0141 :=
    @g_f1oeq1 (.cv x) (.cv y) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0142 :=
    @g_biid (syn_wbr (.cv r) (syn_cwe) (.cv y))
  have p0143 :=
    @g_a1i (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0142
  have p0144 :=
    @g_anbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0141 p0143
  have p0145 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0146 :=
    @g_cnveqd (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0145
  have p0147 :=
    @g_coeq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccnv (.cv f)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r) p0146
  have p0148 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0149 :=
    @g_coeq12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0147 p0148
  have p0150 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r))))
  have p0151 :=
    @g_eqcomi (syn_cpwpull (.cv f) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0150
  have p0152 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))))
  have p0153 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0152
  have p0154 :=
    @g_n_3eqtr3g (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (.cv f) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0149 p0151 p0153
  have p0155 :=
    @g_breq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (.cv f) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (.cv x) (syn_cwe) p0154
  have p0156 :=
    @g_imbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x)) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x)) p0144 p0155
  have p0157 :=
    @g_pwpullwesetimpndv x y f r dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0158 :=
    @g_vtocl (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x))) (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x))) f (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0013 dv_cache_0014 p0140 p0156 p0157
  have p0159 :=
    @g_vtocl (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (.cv x))) (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) x (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0015 dv_cache_0016 p0130 p0137 p0158
  have p0160 :=
    @g_vtocl (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) y (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0017 dv_cache_0018 p0120 p0127 p0159
  have p0161 :=
    @g_vtocl (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) r (syn_cfv (syn_c1st) (.cv u)) dv_cache_0019 dv_cache_0020 p0102 p0117 p0160
  have p0162 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0101 p0161
  have p0163 :=
    @g_syl5eqbrr (.classMem (.cv u) (syn_chwcn D)) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0061 p0162
  have p0164 :=
    @g_imassrn F (syn_cfv (syn_c2nd) (.cv u))
  have p0165 :=
    @g_f1ofo D E F
  have p0166 :=
    Nominal.mp hyp_hnqinctrnvaldndv_2 p0165
  have p0167 :=
    @g_forn D E F
  have p0168 :=
    Nominal.mp p0166 p0167
  have p0169 :=
    @g_sseqtri (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn F) E p0164 p0168
  have p0170 :=
    @g_syl6eqss (.classMem (.cv u) (syn_chwcn D)) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) E p0089 p0169
  have p0171 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E) p0163 p0170
  have p0172 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0173 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0172
  have p0174 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0175 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0173 p0174
  have p0176 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0177 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0176
  have p0178 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0177
  have p0179 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0175 p0178
  have p0180 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0181 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0180
  have p0182 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0181
  have p0183 :=
    @g_elhwcodesclndv (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E p0179 p0182
  have p0184 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wbr (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E)) (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E)) p0171 p0183
  have p0185 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u)))))
  have p0186 :=
    @g_cnvcnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0187 :=
    @g_coeq1i (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0186
  have p0188 :=
    @g_coeq1i (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0187
  have p0189 :=
    @g_eqtri (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0185 p0188
  have p0190 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0189
  have p0191 :=
    @g_f1ofo (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0192 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0096 p0191
  have p0193 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0194 :=
    @g_biid (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0195 :=
    @g_a1i (syn_wb (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0194
  have p0196 :=
    @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0197 :=
    @g_coeq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r) (syn_cfv (syn_c1st) (.cv u)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0196
  have p0198 :=
    @g_coeq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0197
  have p0199 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))))
  have p0200 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0199
  have p0201 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u)))))
  have p0202 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0201
  have p0203 :=
    @g_n_3eqtr3g (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) p0198 p0200 p0202
  have p0204 :=
    @g_sseq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0203
  have p0205 :=
    @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0195 p0204
  have p0206 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0207 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0206
  have p0208 :=
    @g_dmex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0207
  have p0209 :=
    @g_foeq3 (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0210 :=
    @g_biid (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
  have p0211 :=
    @g_a1i (syn_wb (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0210
  have p0212 :=
    @g_imbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0209 p0211
  have p0213 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0214 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0213
  have p0215 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0214
  have p0216 :=
    @g_foeq2 (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0217 :=
    @g_id (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0218 :=
    @g_id (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0219 :=
    @g_xpeq12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0217 p0218
  have p0220 :=
    @g_sseq2d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (.cv x) (.cv x)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0219
  have p0221 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0216 p0220
  have p0222 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0223 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0222
  have p0224 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0223
  have p0225 :=
    @g_foeq1 (.cv x) (.cv y) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0226 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0227 :=
    @g_cnveqd (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0226
  have p0228 :=
    @g_coeq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccnv (.cv f)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r) p0227
  have p0229 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0230 :=
    @g_coeq12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0228 p0229
  have p0231 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r))))
  have p0232 :=
    @g_eqcomi (syn_cpwpull (.cv f) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0231
  have p0233 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))))
  have p0234 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0233
  have p0235 :=
    @g_n_3eqtr3g (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (.cv f) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0230 p0232 p0234
  have p0236 :=
    @g_sseq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (.cv f) (.cv r)) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x)) p0235
  have p0237 :=
    @g_imbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x))) p0225 p0236
  have p0238 :=
    @g_pwpullssxpsetimpndv x y f r dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0239 :=
    @g_vtocl (.imp (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x)))) (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x)))) f (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0013 dv_cache_0021 p0224 p0237 p0238
  have p0240 :=
    @g_vtocl (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (.cv x) (.cv x)))) (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) x (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0015 dv_cache_0022 p0215 p0221 p0239
  have p0241 :=
    @g_vtocl (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) y (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0017 dv_cache_0023 p0208 p0212 p0240
  have p0242 :=
    @g_vtocl (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) r (syn_cfv (syn_c1st) (.cv u)) dv_cache_0019 dv_cache_0024 p0193 p0205 p0241
  have p0243 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0192 p0242
  have p0244 :=
    @g_syl5eqss (.classMem (.cv u) (syn_chwcn D)) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0190 p0243
  have p0245 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0246 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0245
  have p0247 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0248 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0246 p0247
  have p0249 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0250 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0249
  have p0251 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0250
  have p0252 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0248 p0251
  have p0253 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0254 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0253
  have p0255 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0254
  have p0256 :=
    @g_opfv1st (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0252 p0255
  have p0257 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0258 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0257
  have p0259 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0260 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0258 p0259
  have p0261 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0262 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0261
  have p0263 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0262
  have p0264 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0260 p0263
  have p0265 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0266 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0265
  have p0267 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0266
  have p0268 :=
    @g_opfv2nd (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0264 p0267
  have p0269 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0270 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0269
  have p0271 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0272 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0270 p0271
  have p0273 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0274 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0273
  have p0275 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0274
  have p0276 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0272 p0275
  have p0277 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0278 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0277
  have p0279 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0278
  have p0280 :=
    @g_opfv2nd (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0276 p0279
  have p0281 :=
    @g_xpeq12i (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0268 p0280
  have p0282 :=
    @g_sseq12i (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0256 p0281
  have p0283 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wss (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))) p0244 p0282
  have p0284 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))) p0184 p0283
  have p0285 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0286 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0285
  have p0287 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0288 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0286 p0287
  have p0289 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0290 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0289
  have p0291 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0290
  have p0292 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0288 p0291
  have p0293 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0294 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0293
  have p0295 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0294
  have p0296 :=
    @g_opex (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0292 p0295
  have p0297 :=
    @g_elhwcncl E (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0298 :=
    Nominal.mp p0296 p0297
  have p0299 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))))) (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcn E)) p0284 p0298
  have p0300 :=
    @g_syl5eqel (.classMem (.cv u) (syn_chwcn D)) (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcn E) p0056 p0299
  have p0301 :=
    @g_ssv E
  have p0302 :=
    @g_hwcnssbase (syn_cvv) E p0301
  have p0303 :=
    @g_ssel (syn_chwcn E) (syn_chwcn (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u))
  have p0304 :=
    Nominal.mp p0302 p0303
  have p0305 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))) p0300 p0304
  have p0306 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))) p0054 p0305
  have p0307 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0308 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0307
  have p0309 :=
    @g_hwbijf1oclndv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0308
  have p0310 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_chwbij)) p0094 p0309
  have p0311 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0312 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0311
  have p0313 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0314 :=
    @g_hwgenvalclndv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0312 p0313
  have p0315 :=
    @g_opeq2d (.classMem (.cv u) (syn_chwcn D)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) p0084
  have p0316 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0063
  have p0317 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn D)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (.cv u) p0315 p0316
  have p0318 :=
    @g_opeq1d (.classMem (.cv u) (syn_chwcn D)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv u) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0317
  have p0319 :=
    @g_vex u
  have p0320 :=
    @g_hncodetrnfnvalndv u F hyp_hnqinctrnvaldndv_1 p0319
  have p0321 :=
    @g_eqcomi (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0320
  have p0322 :=
    @g_opeq2i (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_chncodetrnfn F) (.cv u)) (.cv u) p0321
  have p0323 :=
    @g_syl6eq (.classMem (.cv u) (syn_chwcn D)) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (.cv u) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0318 p0322
  have p0324 :=
    @g_syl5eq (.classMem (.cv u) (syn_chwcn D)) (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0314 p0323
  have p0325 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0326 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (.classMem (syn_cfv (syn_c1st) (.cv u)) (syn_cvv)) p0324 p0325
  have p0327 :=
    @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0328 :=
    @g_opeq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r) (syn_cfv (syn_c1st) (.cv u)) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0327
  have p0329 :=
    @g_fveq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_chwgen) p0328
  have p0330 :=
    @g_eqeq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))) (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0329
  have p0331 :=
    @g_rspcev (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))) r (syn_cfv (syn_c1st) (.cv u)) (syn_cvv) dv_cache_0019 dv_cache_0025 dv_cache_0026 p0330
  have p0332 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv u)) (syn_cvv)) (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))) p0326 p0331
  have p0333 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_chwbij)) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))) p0310 p0332
  have p0334 :=
    @g_id (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0335 :=
    @g_opeq1d (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r) p0334
  have p0336 :=
    @g_fveq2d (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cop (.cv f) (.cv r)) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)) (syn_chwgen) p0335
  have p0337 :=
    @g_eqeq1d (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0336
  have p0338 :=
    @g_rexbidv (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))) r (syn_cvv) dv_cache_0027 p0337
  have p0339 :=
    @g_rspcev (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))) f (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_chwbij) dv_cache_0028 dv_cache_0029 dv_cache_0030 p0338
  have p0340 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_chwbij)) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))) p0333 p0339
  have p0341 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))) p0306 p0340
  have p0342 :=
    @g_elex (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))
  have p0343 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cvv)) p0305 p0342
  have p0344 :=
    @g_id (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
  have p0345 :=
    @g_breq2d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)) (.cv u) (syn_chwniso (syn_cvv)) p0344
  have p0346 :=
    @g_biid (.classMem (.cv u) (syn_chwcn (syn_cvv)))
  have p0347 :=
    @g_a1i (syn_wb (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (.cv u) (syn_chwcn (syn_cvv)))) (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0346
  have p0348 :=
    @g_id (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
  have p0349 :=
    @g_eleq1d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)) p0348
  have p0350 :=
    @g_anbi12d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (.cv v) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))) p0347 p0349
  have p0351 :=
    @g_id (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
  have p0352 :=
    @g_opeq2d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)) (.cv u) p0351
  have p0353 :=
    @g_eqeq2d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cop (.cv u) (.cv v)) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) p0352
  have p0354 :=
    @g_n_2rexbidv (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))) f r (syn_chwbij) (syn_cvv) dv_cache_0031 dv_cache_0032 p0353
  have p0355 :=
    @g_anbi12d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (.cv v) (syn_chwcn (syn_cvv)))) (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))) p0350 p0354
  have p0356 :=
    @g_bibi12d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (.cv v)) (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (.cv v) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))) p0345 p0355
  have p0357 :=
    @g_elhwnisogen v u (syn_cvv) f r dv_cache_0033 dv_cache_0025 dv_cache_0007 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
  have p0358 :=
    @g_vtoclg (syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (.cv v) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))))))) (syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))))) v (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cvv) dv_cache_0038 dv_cache_0039 p0356 p0357
  have p0359 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cvv)) (syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))))) p0343 p0358
  have p0360 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))) p0341 p0359
  have p0361 :=
    @g_hwcnssbase A E hyp_hnqinctrnvaldndv_4
  have p0362 :=
    @g_ssel (syn_chwcn E) (syn_chwcn A) (syn_cfv (syn_chncodetrnfn F) (.cv u))
  have p0363 :=
    Nominal.mp p0361 p0362
  have p0364 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)) p0300 p0363
  have p0365 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)) p0019 p0364
  have p0366 :=
    @g_ssv A
  have p0367 :=
    @g_hwnisobasebicl (syn_cvv) (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)) A p0366
  have p0368 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_wbr (.cv u) (syn_chwniso A) (syn_cfv (syn_chncodetrnfn F) (.cv u)))) p0365 p0367
  have p0369 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_wbr (.cv u) (syn_chwniso A) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0360 p0368
  have p0370 :=
    @g_hwnisoclasseqbcl A (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)) hyp_hnqinctrnvaldndv_5
  have p0371 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A))) (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chwniso A) (syn_cfv (syn_chncodetrnfn F) (.cv u)))) p0365 p0370
  have p0372 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chwniso A) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0369 p0371
  have p0373 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn D)) (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) p0049 p0372
  have p0374 :=
    @g_f1ofo D E F
  have p0375 :=
    Nominal.mp hyp_hnqinctrnvaldndv_2 p0374
  have p0376 :=
    @g_forn D E F
  have p0377 :=
    Nominal.mp p0375 p0376
  have p0378 :=
    @g_rnex F hyp_hnqinctrnvaldndv_1
  have p0379 :=
    @g_eqeltrri (syn_crn F) E (syn_cvv) p0377 p0378
  have p0380 :=
    @g_hnqmap1valcl E (syn_cfv (syn_chncodetrnfn F) (.cv u)) p0379
  have p0381 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)) (.classEq (syn_cfv (syn_chnqmap1 E) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) p0300 p0380
  have p0382 :=
    @g_snelpw1 (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)
  have p0383 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)) (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn E))) p0300 p0382
  have p0384 :=
    @g_hnqmap1fn E p0379
  have p0385 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn E))) (syn_wfn (syn_chnqmap1 E) (syn_cpw1 (syn_chwcn E))) p0383 p0384
  have p0386 :=
    @g_fnbrfvb (syn_cpw1 (syn_chwcn E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnqmap1 E)
  have p0387 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wfn (syn_chnqmap1 E) (syn_cpw1 (syn_chwcn E))) (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn E)))) (syn_wb (.classEq (syn_cfv (syn_chnqmap1 E) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 E) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))) p0385 p0386
  have p0388 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqmap1 E) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 E) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) p0381 p0387
  have p0389 :=
    @g_brcnv (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 E)
  have p0390 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 E) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) p0388 p0389
  have p0391 :=
    @g_hnqmap1valcl A (syn_cfv (syn_chncodetrnfn F) (.cv u)) hyp_hnqinctrnvaldndv_5
  have p0392 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) p0364 p0391
  have p0393 :=
    @g_snelpw1 (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)
  have p0394 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)) (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn A))) p0364 p0393
  have p0395 :=
    @g_hnqmap1fn A hyp_hnqinctrnvaldndv_5
  have p0396 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn A))) (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) p0394 p0395
  have p0397 :=
    @g_fnbrfvb (syn_cpw1 (syn_chwcn A)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqmap1 A)
  have p0398 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn A)))) (syn_wb (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))) p0396 p0397
  have p0399 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) p0392 p0398
  have p0400 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) p0390 p0399
  have p0401 :=
    @g_snex (syn_cfv (syn_chncodetrnfn F) (.cv u))
  have p0402 :=
    @g_id (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
  have p0403 :=
    @g_breq2d (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) p0402
  have p0404 :=
    @g_id (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
  have p0405 :=
    @g_breq1d (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqmap1 A) p0404
  have p0406 :=
    @g_anbi12d (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (.cv x)) (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) p0403 p0405
  have p0407 :=
    @g_spcev (syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (.cv x)) (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))) (syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))) x (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) dv_cache_0040 dv_cache_0041 p0401 p0406
  have p0408 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))) (syn_wex x (syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (.cv x)) (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))))) p0400 p0407
  have p0409 :=
    @g_brco x (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 E)) dv_cache_0042 dv_cache_0043 dv_cache_0005 dv_cache_0044
  have p0410 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wex x (syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccnv (syn_chnqmap1 E)) (.cv x)) (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))))) (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 E))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) p0408 p0409
  have p0411 :=
    (by simpa [syn_chnqinc] using (Nominal.classEqRefl (syn_chnqinc E A)))
  have p0412 :=
    @g_breqi (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqinc E A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 E))) p0411
  have p0413 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 E))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) p0410 p0412
  have p0414 :=
    @g_hwnisoclasselhnordcl E (syn_cfv (syn_chncodetrnfn F) (.cv u)) p0379
  have p0415 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)) (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnord E)) p0300 p0414
  have p0416 :=
    @g_hnqincfn A E hyp_hnqinctrnvaldndv_4 p0379 hyp_hnqinctrnvaldndv_5
  have p0417 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnord E)) (syn_wfn (syn_chnqinc E A) (syn_chnord E)) p0415 p0416
  have p0418 :=
    @g_fnbrfvb (syn_chnord E) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqinc E A)
  have p0419 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wfn (syn_chnqinc E A) (syn_chnord E)) (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnord E))) (syn_wb (.classEq (syn_cfv (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))) p0417 p0418
  have p0420 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))) p0413 p0419
  have p0421 :=
    @g_eqtr4d (.classMem (.cv u) (syn_chwcn D)) (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_cfv (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) p0373 p0420
  exact p0421

#print axioms g_hnqinctrnvaldndv

end NFChoice.DirectNominalPrf.WPPReplay
