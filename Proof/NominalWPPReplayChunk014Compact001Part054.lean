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
import NominalWPPReplayChunk014Compact001Part053

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

noncomputable def g_lefinssvvk
     :
    Nominal.NPrf (syn_wss (syn_clefin) (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_w_ne_x : w ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have dv_cache_0001 : w ≠ x := by
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0002 : w ≠ y := by
    clear dv_cache_0001
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0003 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lefin x y z w dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_opkabssvvki (syn_wrex w (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv y) (.cv w)))) x y z (syn_clefin) dv_cache_0004 dv_cache_0005 p0000
  exact p0001

noncomputable def g_ltfinssvvk
     :
    Nominal.NPrf (syn_wss (syn_cltfin) (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let m : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_m_ne_n : m ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_m : n ≠ m :=
    Ne.symm fresh_m_ne_n
  have fresh_m_ne_p : m ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_m : p ≠ m :=
    Ne.symm fresh_m_ne_p
  have fresh_m_ne_x : m ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_m : x ≠ m :=
    Ne.symm fresh_m_ne_x
  have fresh_n_ne_p : n ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_n : p ≠ n :=
    Ne.symm fresh_n_ne_p
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_p_ne_x : p ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have dv_cache_0001 : m ≠ n := by
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0002 : m ≠ p := by
    clear dv_cache_0001
    exact (show m ≠ p from (by exact fresh_m_ne_p))
  have dv_cache_0003 : m ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0004 : n ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show n ≠ p from (by exact fresh_n_ne_p))
  have dv_cache_0005 : n ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0006 : p ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0007 : x ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ m from (by exact fresh_x_ne_m))
  have dv_cache_0008 : x ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ n from (by exact fresh_x_ne_n))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ltfin x m n p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_opkabssvvki (syn_wa (syn_wne (.cv m) (syn_c0)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c))))) x m n (syn_cltfin) dv_cache_0007 dv_cache_0008 p0000
  exact p0001

noncomputable def g_ltfinunidkssvvk
     :
    Nominal.NPrf (syn_wss (syn_cun (syn_cltfin) (syn_cidk)) (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_ltfinssvvk
  have p0001 :=
    @g_idkssvvk
  have p0002 :=
    @g_unssi (syn_cltfin) (syn_cidk) (syn_cxpk (syn_cvv) (syn_cvv)) p0000 p0001
  exact p0002

noncomputable def g_ellefinunidk
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_cun (syn_cltfin) (syn_cidk))) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_elun (syn_copk A B) (syn_cltfin) (syn_cidk)
  have p0001 :=
    @g_a1i (syn_wb (.classMem (syn_copk A B) (syn_cun (syn_cltfin) (syn_cidk))) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk A B) (syn_cidk)))) (syn_wa (.classMem A V) (.classMem B W)) p0000
  have p0002 :=
    @g_opkelidkg A B V W
  have p0003 :=
    @g_orbi2d (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_copk A B) (syn_cidk)) (.classEq A B) (.classMem (syn_copk A B) (syn_cltfin)) p0002
  have p0004 :=
    @g_bitrd (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_copk A B) (syn_cun (syn_cltfin) (syn_cidk))) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk A B) (syn_cidk))) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0001 p0003
  exact p0004

noncomputable def g_lefinlteq0
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_V, fresh_x_not_B, fresh_x_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simp1 (.classMem A V) (.classMem B W) (.classEq A (syn_c0))
  have p0001 :=
    @g_simp2 (.classMem A V) (.classMem B W) (.classEq A (syn_c0))
  have p0002 :=
    @g_jca (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem A V) (.classMem B W) p0000 p0001
  have p0003 :=
    @g_opklefing x A B V W dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_syl (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))) p0002 p0003
  have p0005 :=
    @g_simpl (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x)))
  have p0006 :=
    @g_simpl (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))
  have p0007 :=
    @g_simp3 (.classMem A V) (.classMem B W) (.classEq A (syn_c0))
  have p0008 :=
    @g_syl (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A (syn_c0)) p0006 p0007
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x)))) (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq A (syn_c0)) p0005 p0008
  have p0010 :=
    @g_simpr (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x)))
  have p0011 :=
    @g_simpl (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x)))
  have p0012 :=
    @g_addccom A (.cv x)
  have p0013 :=
    @g_a1i (.classEq (syn_cplc A (.cv x)) (syn_cplc (.cv x) A)) (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) p0012
  have p0014 :=
    @g_simpl (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))
  have p0015 :=
    @g_simp3 (.classMem A V) (.classMem B W) (.classEq A (syn_c0))
  have p0016 :=
    @g_syl (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A (syn_c0)) p0014 p0015
  have p0017 :=
    @g_addceq2d (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) A (syn_c0) (.cv x) p0016
  have p0018 :=
    @g_eqtrd (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (syn_cplc A (.cv x)) (syn_cplc (.cv x) A) (syn_cplc (.cv x) (syn_c0)) p0013 p0017
  have p0019 :=
    @g_addcnul1 (.cv x)
  have p0020 :=
    @g_a1i (.classEq (syn_cplc (.cv x) (syn_c0)) (syn_c0)) (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) p0019
  have p0021 :=
    @g_eqtrd (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (syn_cplc A (.cv x)) (syn_cplc (.cv x) (syn_c0)) (syn_c0) p0018 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x)))) (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq (syn_cplc A (.cv x)) (syn_c0)) p0011 p0021
  have p0023 :=
    @g_eqtrd (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x)))) B (syn_cplc A (.cv x)) (syn_c0) p0010 p0022
  have p0024 :=
    @g_eqcomd (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x)))) B (syn_c0) p0023
  have p0025 :=
    @g_eqtrd (syn_wa (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x)))) A (syn_c0) B p0009 p0024
  have p0026 :=
    @g_ex (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (.cv x) (syn_cnnc))) (.classEq B (syn_cplc A (.cv x))) (.classEq A B) p0025
  have p0027 :=
    @g_rexlimdva (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq B (syn_cplc A (.cv x))) (.classEq A B) x (syn_cnnc) dv_cache_0003 dv_cache_0004 p0026
  have p0028 :=
    @g_sylbid (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (syn_copk A B) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (.classEq A B) p0004 p0027
  have p0029 :=
    @g_simpl (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B)
  have p0030 :=
    @g_simp1 (.classMem A V) (.classMem B W) (.classEq A (syn_c0))
  have p0031 :=
    @g_syl (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B)) (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem A V) p0029 p0030
  have p0032 :=
    @g_lefinrflx A V
  have p0033 :=
    @g_syl (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B)) (.classMem A V) (.classMem (syn_copk A A) (syn_clefin)) p0031 p0032
  have p0034 :=
    @g_simpr (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B)
  have p0035 :=
    @g_opkeq2 A B A
  have p0036 :=
    @g_syl (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B)) (.classEq A B) (.classEq (syn_copk A A) (syn_copk A B)) p0034 p0035
  have p0037 :=
    @g_eleq1d (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B)) (syn_copk A A) (syn_copk A B) (syn_clefin) p0036
  have p0038 :=
    @g_mpbid (syn_wa (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B)) (.classMem (syn_copk A A) (syn_clefin)) (.classMem (syn_copk A B) (syn_clefin)) p0033 p0037
  have p0039 :=
    @g_ex (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classEq A B) (.classMem (syn_copk A B) (syn_clefin)) p0038
  have p0040 :=
    @g_impbid (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B) p0028 p0039
  exact p0040

noncomputable def g_lefinlteqall
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))
  have p0001 :=
    @g_simpl (.classMem A V) (.classMem B W)
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))) (syn_wa (.classMem A V) (.classMem B W)) (.classMem A V) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))
  have p0004 :=
    @g_simpr (.classMem A V) (.classMem B W)
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))) (syn_wa (.classMem A V) (.classMem B W)) (.classMem B W) p0003 p0004
  have p0006 :=
    @g_simpr (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))
  have p0007 :=
    @g_n_3jca (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))) (.classMem A V) (.classMem B W) (syn_wne A (syn_c0)) p0002 p0005 p0006
  have p0008 :=
    @g_lefinlteq A B V W
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))) (syn_w3a (.classMem A V) (.classMem B W) (syn_wne A (syn_c0))) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B))) p0007 p0008
  have p0010 :=
    @g_ex (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0)) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B))) p0009
  have p0011 :=
    @g_simpl (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))
  have p0012 :=
    @g_simpl (.classMem A V) (.classMem B W)
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (syn_wa (.classMem A V) (.classMem B W)) (.classMem A V) p0011 p0012
  have p0014 :=
    @g_simpl (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))
  have p0015 :=
    @g_simpr (.classMem A V) (.classMem B W)
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (syn_wa (.classMem A V) (.classMem B W)) (.classMem B W) p0014 p0015
  have p0017 :=
    @g_simpr (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))
  have p0018 :=
    @g_nne A (syn_c0)
  have p0019 :=
    @g_a1i (syn_wb (.neg (syn_wne A (syn_c0))) (.classEq A (syn_c0))) (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) p0018
  have p0020 :=
    @g_mpbid (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (.neg (syn_wne A (syn_c0))) (.classEq A (syn_c0)) p0017 p0019
  have p0021 :=
    @g_n_3jca (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (.classMem A V) (.classMem B W) (.classEq A (syn_c0)) p0013 p0016 p0020
  have p0022 :=
    @g_lefinlteq0 A B V W
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (syn_w3a (.classMem A V) (.classMem B W) (.classEq A (syn_c0))) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B)) p0021 p0022
  have p0024 :=
    @g_simpr (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))
  have p0025 :=
    @g_simpl (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))
  have p0026 :=
    @g_opkltfing x A B V W dv_cache_0001 dv_cache_0002
  have p0027 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))) p0025 p0026
  have p0028 :=
    @g_simpl (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
  have p0029 :=
    @g_a1i (.imp (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) (syn_wne A (syn_c0))) (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) p0028
  have p0030 :=
    @g_sylbid (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) (syn_wne A (syn_c0)) p0027 p0029
  have p0031 :=
    @g_con3d (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (.classMem (syn_copk A B) (syn_cltfin)) (syn_wne A (syn_c0)) p0030
  have p0032 :=
    @g_mpd (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (.neg (syn_wne A (syn_c0))) (.neg (.classMem (syn_copk A B) (syn_cltfin))) p0024 p0031
  have p0033 :=
    @g_biorf (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (.neg (.classMem (syn_copk A B) (syn_cltfin))) (syn_wb (.classEq A B) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B))) p0032 p0033
  have p0035 :=
    @g_bitrd (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0)))) (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0023 p0034
  have p0036 :=
    @g_ex (syn_wa (.classMem A V) (.classMem B W)) (.neg (syn_wne A (syn_c0))) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B))) p0035
  have p0037 :=
    @g_pm2_61d (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0)) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B))) p0010 p0036
  exact p0037

noncomputable def g_lefinunidk
     :
    Nominal.NPrf (.classEq (syn_clefin) (syn_cun (syn_cltfin) (syn_cidk))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_clefin)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_clefin)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cun (syn_cltfin) (syn_cidk))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cun (syn_cltfin) (syn_cidk))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_lefinssvvk
  have p0001 :=
    @g_ltfinunidkssvvk
  have p0002 :=
    @g_tru
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) syn_wtru p0003
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_a1i (.classMem (.cv y) (syn_cvv)) syn_wtru p0005
  have p0007 :=
    @g_jca syn_wtru (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0004 p0006
  have p0008 :=
    Nominal.mp p0002 p0007
  have p0009 :=
    @g_lefinlteqall (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_tru
  have p0012 :=
    @g_vex x
  have p0013 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) syn_wtru p0012
  have p0014 :=
    @g_vex y
  have p0015 :=
    @g_a1i (.classMem (.cv y) (syn_cvv)) syn_wtru p0014
  have p0016 :=
    @g_jca syn_wtru (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0013 p0015
  have p0017 :=
    Nominal.mp p0011 p0016
  have p0018 :=
    @g_ellefinunidk (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_bitr4i (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (syn_wo (.classMem (syn_copk (.cv x) (.cv y)) (syn_cltfin)) (.classEq (.cv x) (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cun (syn_cltfin) (syn_cidk))) p0010 p0019
  have p0021 :=
    @g_eqrelkriiv x y (syn_clefin) (syn_cun (syn_cltfin) (syn_cidk)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0000 p0001 p0020
  exact p0021

noncomputable def g_lefinex
     :
    Nominal.NPrf (.classMem (syn_clefin) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_lefinunidk
  have p0001 :=
    @g_ltfinex
  have p0002 :=
    @g_idkex
  have p0003 :=
    @g_unex (syn_cltfin) (syn_cidk) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_clefin) (syn_cun (syn_cltfin) (syn_cidk)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_kqrelbrg
    (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem B V) (.classMem C W)) (syn_wb (.classMem (syn_cop B C) (syn_ckqrel A)) (.classMem (syn_copk B C) A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (syn_copk B C) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classMem (syn_copk B C) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_C, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_kqrel x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eleq2i (syn_ckqrel A) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A)) (syn_cop B C) p0000
  have p0002 :=
    @g_a1i (syn_wb (.classMem (syn_cop B C) (syn_ckqrel A)) (.classMem (syn_cop B C) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A)))) (syn_wa (.classMem B V) (.classMem C W)) p0001
  have p0003 :=
    @g_opkeq1 (.cv x) B (.cv y)
  have p0004 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_copk (.cv x) (.cv y)) (syn_copk B (.cv y)) A p0003
  have p0005 :=
    @g_opkeq2 (.cv y) C B
  have p0006 :=
    @g_eleq1d (.classEq (.cv y) C) (syn_copk B (.cv y)) (syn_copk B C) A p0005
  have p0007 :=
    @g_opelopabg (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk B (.cv y)) A) (.classMem (syn_copk B C) A) x y B C V W dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0003 p0004 p0006
  have p0008 :=
    @g_bitrd (syn_wa (.classMem B V) (.classMem C W)) (.classMem (syn_cop B C) (syn_ckqrel A)) (.classMem (syn_cop B C) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A))) (.classMem (syn_copk B C) A) p0002 p0007
  exact p0008

noncomputable def g_kqlefinbr
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (syn_wbr A (syn_ckqrel (syn_clefin)) B) (.classMem (syn_copk A B) (syn_clefin)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A (syn_ckqrel (syn_clefin)) B)))
  have p0001 :=
    @g_a1i (syn_wb (syn_wbr A (syn_ckqrel (syn_clefin)) B) (.classMem (syn_cop A B) (syn_ckqrel (syn_clefin)))) (syn_wa (.classMem A V) (.classMem B W)) p0000
  have p0002 :=
    @g_kqrelbrg (syn_clefin) A B V W
  have p0003 :=
    @g_bitrd (syn_wa (.classMem A V) (.classMem B W)) (syn_wbr A (syn_ckqrel (syn_clefin)) B) (.classMem (syn_cop A B) (syn_ckqrel (syn_clefin))) (.classMem (syn_copk A B) (syn_clefin)) p0001 p0002
  exact p0003

noncomputable def g_lefintrnn
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin))) (.classMem (syn_copk A C) (syn_clefin)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_simpr (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0001 :=
    @g_simpr (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin))
  have p0002 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin))) (.classMem (syn_copk B C) (syn_clefin)) p0000 p0001
  have p0003 :=
    @g_simpl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0004 :=
    @g_simp2 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0005 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem B (syn_cnnc)) p0003 p0004
  have p0006 :=
    @g_simpl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0007 :=
    @g_simp3 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0008 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem C (syn_cnnc)) p0006 p0007
  have p0009 :=
    @g_jca (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)) p0005 p0008
  have p0010 :=
    @g_lenltfin B C
  have p0011 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_wa (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wb (.classMem (syn_copk B C) (syn_clefin)) (.neg (.classMem (syn_copk C B) (syn_cltfin)))) p0009 p0010
  have p0012 :=
    @g_biimpd (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem (syn_copk B C) (syn_clefin)) (.neg (.classMem (syn_copk C B) (syn_cltfin))) p0011
  have p0013 :=
    @g_mpd (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem (syn_copk B C) (syn_clefin)) (.neg (.classMem (syn_copk C B) (syn_cltfin))) p0002 p0012
  have p0014 :=
    @g_simpr (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0015 :=
    @g_simpl (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin))
  have p0016 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin))) (.classMem (syn_copk A B) (syn_clefin)) p0014 p0015
  have p0017 :=
    @g_simpl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0018 :=
    @g_simp1 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0019 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem A (syn_cnnc)) p0017 p0018
  have p0020 :=
    @g_elex A (syn_cnnc)
  have p0021 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_simpl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0023 :=
    @g_simp2 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0024 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem B (syn_cnnc)) p0022 p0023
  have p0025 :=
    @g_elex B (syn_cnnc)
  have p0026 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0024 p0025
  have p0027 :=
    @g_jca (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0021 p0026
  have p0028 :=
    @g_lefinlteqall A B (syn_cvv) (syn_cvv)
  have p0029 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B))) p0027 p0028
  have p0030 :=
    @g_biimpd (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0029
  have p0031 :=
    @g_mpd (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0016 p0030
  have p0032 :=
    @g_simpl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0033 :=
    @g_simp3 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0034 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem C (syn_cnnc)) p0032 p0033
  have p0035 :=
    @g_simpl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0036 :=
    @g_simp1 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0037 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem A (syn_cnnc)) p0035 p0036
  have p0038 :=
    @g_simpl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0039 :=
    @g_simp2 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0040 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem B (syn_cnnc)) p0038 p0039
  have p0041 :=
    @g_n_3jca (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem C (syn_cnnc)) (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) p0034 p0037 p0040
  have p0042 :=
    @g_ltfintr C A B
  have p0043 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem C (syn_cnnc)) (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk A B) (syn_cltfin))) (.classMem (syn_copk C B) (syn_cltfin))) p0041 p0042
  have p0044 :=
    @g_exp3a (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin)) p0043
  have p0045 :=
    @g_com23 (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin)) p0044
  have p0046 :=
    @g_opkeq2 A B C
  have p0047 :=
    @g_eleq1d (.classEq A B) (syn_copk C A) (syn_copk C B) (syn_cltfin) p0046
  have p0048 :=
    @g_biimpd (.classEq A B) (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin)) p0047
  have p0049 :=
    @g_a1i (.imp (.classEq A B) (.imp (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin)))) (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) p0048
  have p0050 :=
    @g_jaod (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem (syn_copk A B) (syn_cltfin)) (.imp (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin))) (.classEq A B) p0045 p0049
  have p0051 :=
    @g_mpd (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) (.imp (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin))) p0031 p0050
  have p0052 :=
    @g_con3d (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem (syn_copk C A) (syn_cltfin)) (.classMem (syn_copk C B) (syn_cltfin)) p0051
  have p0053 :=
    @g_mpd (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.neg (.classMem (syn_copk C B) (syn_cltfin))) (.neg (.classMem (syn_copk C A) (syn_cltfin))) p0013 p0052
  have p0054 :=
    @g_simpl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0055 :=
    @g_simp1 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0056 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem A (syn_cnnc)) p0054 p0055
  have p0057 :=
    @g_simpl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))
  have p0058 :=
    @g_simp3 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
  have p0059 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem C (syn_cnnc)) p0057 p0058
  have p0060 :=
    @g_jca (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)) p0056 p0059
  have p0061 :=
    @g_lenltfin A C
  have p0062 :=
    @g_syl (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wb (.classMem (syn_copk A C) (syn_clefin)) (.neg (.classMem (syn_copk C A) (syn_cltfin)))) p0060 p0061
  have p0063 :=
    @g_biimprd (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.classMem (syn_copk A C) (syn_clefin)) (.neg (.classMem (syn_copk C A) (syn_cltfin))) p0062
  have p0064 :=
    @g_mpd (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin)))) (.neg (.classMem (syn_copk C A) (syn_cltfin))) (.classMem (syn_copk A C) (syn_clefin)) p0053 p0063
  have p0065 :=
    @g_ex (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_clefin))) (.classMem (syn_copk A C) (syn_clefin)) p0064
  exact p0065

#print axioms g_lefintrnn

end NFChoice.DirectNominalPrf.WPPReplay
