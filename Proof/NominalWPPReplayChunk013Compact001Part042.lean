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
import NominalWPPReplayChunk013Compact001Part041

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

noncomputable def g_brlec
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) (hyp_brlec_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_brlec_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_clec) B) (syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_brlecg x y A B (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (syn_wbr A (syn_clec) B) (syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y))))) hyp_brlec_1 hyp_brlec_2 p0000
  exact p0001

noncomputable def g_brltc
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cltc) B) (syn_wa (syn_wbr A (syn_clec) B) (syn_wne A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_brex A B (syn_cltc)
  have p0001 :=
    @g_simprd (syn_wbr A (syn_cltc) B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0000
  have p0002 :=
    @g_brex A B (syn_clec)
  have p0003 :=
    @g_simprd (syn_wbr A (syn_clec) B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0002
  have p0004 :=
    @g_adantr (syn_wbr A (syn_clec) B) (.classMem B (syn_cvv)) (syn_wne A B) p0003
  have p0005 :=
    (by simpa [syn_cltc] using (Nominal.classEqRefl (syn_cltc)))
  have p0006 :=
    @g_breqi A B (syn_cltc) (syn_cdif (syn_clec) (syn_cid)) p0005
  have p0007 :=
    @g_brdif A B (syn_clec) (syn_cid)
  have p0008 :=
    @g_bitri (syn_wbr A (syn_cltc) B) (syn_wbr A (syn_cdif (syn_clec) (syn_cid)) B) (syn_wa (syn_wbr A (syn_clec) B) (.neg (syn_wbr A (syn_cid) B))) p0006 p0007
  have p0009 :=
    @g_ideqg A B (syn_cvv)
  have p0010 :=
    @g_necon3bbid (.classMem B (syn_cvv)) (syn_wbr A (syn_cid) B) A B p0009
  have p0011 :=
    @g_anbi2d (.classMem B (syn_cvv)) (.neg (syn_wbr A (syn_cid) B)) (syn_wne A B) (syn_wbr A (syn_clec) B) p0010
  have p0012 :=
    @g_syl5bb (syn_wbr A (syn_cltc) B) (syn_wa (syn_wbr A (syn_clec) B) (.neg (syn_wbr A (syn_cid) B))) (.classMem B (syn_cvv)) (syn_wa (syn_wbr A (syn_clec) B) (syn_wne A B)) p0008 p0011
  have p0013 :=
    @g_pm5_21nii (syn_wbr A (syn_cltc) B) (.classMem B (syn_cvv)) (syn_wa (syn_wbr A (syn_clec) B) (syn_wne A B)) p0001 p0004 p0012
  exact p0013

noncomputable def g_lecex
     :
    Nominal.NPrf (.classMem (syn_clec) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let u : Var := freshVar proofSupport 5
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_t : a ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_a : t ≠ a :=
    Ne.symm fresh_a_ne_t
  have fresh_a_ne_u : a ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_u_ne_a : u ≠ a :=
    Ne.symm fresh_a_ne_u
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_ne_t : b ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_b : t ≠ b :=
    Ne.symm fresh_b_ne_t
  have fresh_b_ne_u : b ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_u_ne_b : u ≠ b :=
    Ne.symm fresh_b_ne_u
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have dv_cache_0001 : y ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0003 : t ∉ ((syn_wss (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((syn_wss (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_csn (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((syn_csn (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_a, fresh_u_ne_y, fresh_u_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, fresh_t_ne_u, fresh_t_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : t ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0012 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : t ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((syn_ccom (syn_csset) (syn_csi (syn_csset)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((syn_ccnv (syn_csset))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : u ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : u ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : u ∉ ((syn_csset)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : u ∉ ((syn_csi (syn_csset))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : x ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((syn_csset)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((syn_csset)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : u ∉ ((syn_wbr (.cv t) (syn_csset) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_t, fresh_u_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : x ∉ ((syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_a, fresh_x_ne_u, fresh_x_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : y ∉ ((syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_a, fresh_y_ne_u, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : a ∉ ((syn_clec)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((syn_clec)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : a ∉ ((syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : b ∉ ((syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    @g_r2ex (syn_wss (.cv x) (.cv y)) x y (.cv a) (.cv b) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_n_19_41vv (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))) (syn_wss (.cv x) (.cv y)) t u dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_anass (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))
  have p0003 :=
    @g_n_2exbii (syn_wa (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))) (syn_wss (.cv x) (.cv y))) (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))) t u p0002
  have p0004 :=
    @g_ancom (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))
  have p0005 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))))))
  have p0006 :=
    @g_bitr4i (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))) (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))) p0004 p0005
  have p0007 :=
    @g_n_2exbii (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))) (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))) t u p0006
  have p0008 :=
    @g_snex (.cv x)
  have p0009 :=
    @g_snex (.cv y)
  have p0010 :=
    @g_breq1 (.cv t) (syn_csn (.cv x)) (.cv a) (syn_csset)
  have p0011 :=
    @g_anbi1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)) p0010
  have p0012 :=
    @g_breq1 (.cv u) (syn_csn (.cv y)) (.cv b) (syn_csset)
  have p0013 :=
    @g_anbi2d (.classEq (.cv u) (syn_csn (.cv y))) (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)) (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) p0012
  have p0014 :=
    @g_ceqsex2v (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b))) t u (syn_csn (.cv x)) (syn_csn (.cv y)) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0008 p0009 p0011 p0013
  have p0015 :=
    @g_vex x
  have p0016 :=
    @g_vex a
  have p0017 :=
    @g_brssetsn (.cv x) (.cv a) p0015 p0016
  have p0018 :=
    @g_vex y
  have p0019 :=
    @g_vex b
  have p0020 :=
    @g_brssetsn (.cv y) (.cv b) p0018 p0019
  have p0021_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0017
  have p0021_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)) (.objMem y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0020
  have p0021 :=
    @g_anbi12i (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (.objMem x a) (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b)) (.objMem y b) p0021_e00_recanon p0021_e01_recanon
  have p0022 :=
    @g_n_3bitri (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))))) (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)))))) (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_csset) (.cv a)) (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv b))) (syn_wa (.objMem x a) (.objMem y b)) p0007 p0014 p0021
  have p0023 :=
    @g_anbi1i (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))))) (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y)) p0022
  have p0024 :=
    @g_n_3bitr3i (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))) (syn_wss (.cv x) (.cv y))))) (syn_wa (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))))))) (syn_wss (.cv x) (.cv y))) (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))) (syn_wa (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y))) p0001 p0003 p0023
  have p0025 :=
    @g_n_2exbii (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))) (syn_wa (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y))) x y p0024
  have p0026_e00_recanon : Nominal.NPrf (syn_wb (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y)))) (syn_wex x (syn_wex y (syn_wa (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0026 :=
    @g_bitr4i (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y)))) (syn_wex x (syn_wex y (syn_wa (syn_wa (.objMem x a) (.objMem y b)) (syn_wss (.cv x) (.cv y))))) (syn_wex x (syn_wex y (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))) p0026_e00_recanon p0025
  have p0027 :=
    @g_brlec x y (.cv a) (.cv b) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0002 p0016 p0019
  have p0028 :=
    @g_brco t (.cv a) (.cv b) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset)) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0029 :=
    @g_brcnv (.cv a) (.cv t) (syn_csset)
  have p0030 :=
    @g_brco u (.cv t) (.cv b) (syn_csset) (syn_csi (syn_csset)) dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
  have p0031 :=
    @g_brsi x y (.cv t) (.cv u) (syn_csset) dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0002
  have p0032 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (syn_wbr (.cv x) (syn_csset) (.cv y)))))
  have p0033 :=
    @g_brsset (.cv x) (.cv y) p0015 p0018
  have p0034 :=
    @g_anbi2i (syn_wbr (.cv x) (syn_csset) (.cv y)) (syn_wss (.cv x) (.cv y)) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) p0033
  have p0035 :=
    @g_bitri (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (syn_wbr (.cv x) (syn_csset) (.cv y))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wbr (.cv x) (syn_csset) (.cv y))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))) p0032 p0034
  have p0036 :=
    @g_n_2exbii (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (syn_wbr (.cv x) (syn_csset) (.cv y))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))) x y p0035
  have p0037 :=
    @g_bitri (syn_wbr (.cv t) (syn_csi (syn_csset)) (.cv u)) (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (syn_wbr (.cv x) (syn_csset) (.cv y))))) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))) p0031 p0036
  have p0038 :=
    @g_anbi2ci (syn_wbr (.cv t) (syn_csi (syn_csset)) (.cv u)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))) (syn_wbr (.cv u) (syn_csset) (.cv b)) p0037
  have p0039 :=
    @g_exbii (syn_wa (syn_wbr (.cv t) (syn_csi (syn_csset)) (.cv u)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))) u p0038
  have p0040 :=
    @g_bitri (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b)) (syn_wex u (syn_wa (syn_wbr (.cv t) (syn_csi (syn_csset)) (.cv u)) (syn_wbr (.cv u) (syn_csset) (.cv b)))) (syn_wex u (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))) p0030 p0039
  have p0041 :=
    @g_anbi12i (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t)) (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b)) (syn_wex u (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))) p0029 p0040
  have p0042 :=
    @g_n_19_42v (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))) u dv_cache_0029
  have p0043 :=
    @g_n_19_42vv (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))) x y dv_cache_0030 dv_cache_0031
  have p0044 :=
    @g_anass (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))
  have p0045 :=
    @g_bitr2i (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))) (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))) (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))) p0043 p0044
  have p0046 :=
    @g_exbii (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))) (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))) u p0045
  have p0047 :=
    @g_n_3bitr2i (syn_wa (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t)) (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b))) (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wex u (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))) (syn_wex u (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wa (syn_wbr (.cv u) (syn_csset) (.cv b)) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))) (syn_wex u (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))) p0041 p0042 p0046
  have p0048 :=
    @g_exbii (syn_wa (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t)) (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b))) (syn_wex u (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y))))))) t p0047
  have p0049 :=
    @g_exrot4 (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))) t u x y
  have p0050 :=
    @g_n_3bitri (syn_wbr (.cv a) (syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset))) (.cv b)) (syn_wex t (syn_wa (syn_wbr (.cv a) (syn_ccnv (syn_csset)) (.cv t)) (syn_wbr (.cv t) (syn_ccom (syn_csset) (syn_csi (syn_csset))) (.cv b)))) (syn_wex t (syn_wex u (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))) (syn_wex x (syn_wex y (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))) p0028 p0048 p0049
  have p0051 :=
    @g_n_3bitr4i (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y)))) (syn_wex x (syn_wex y (syn_wex t (syn_wex u (syn_wa (syn_wa (syn_wbr (.cv t) (syn_csset) (.cv a)) (syn_wbr (.cv u) (syn_csset) (.cv b))) (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))) (syn_wss (.cv x) (.cv y)))))))) (syn_wbr (.cv a) (syn_clec) (.cv b)) (syn_wbr (.cv a) (syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset))) (.cv b)) p0026 p0027 p0050
  have p0052 :=
    @g_eqbrriv a b (syn_clec) (syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset))) dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 p0051
  have p0053 :=
    @g_ssetex
  have p0054 :=
    @g_ssetex
  have p0055 :=
    @g_siex (syn_csset) p0054
  have p0056 :=
    @g_coex (syn_csset) (syn_csi (syn_csset)) p0053 p0055
  have p0057 :=
    @g_ssetex
  have p0058 :=
    @g_cnvex (syn_csset) p0057
  have p0059 :=
    @g_coex (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset)) p0056 p0058
  have p0060 :=
    @g_eqeltri (syn_clec) (syn_ccom (syn_ccom (syn_csset) (syn_csi (syn_csset))) (syn_ccnv (syn_csset))) (syn_cvv) p0052 p0059
  exact p0060

noncomputable def g_ltcex
     :
    Nominal.NPrf (.classMem (syn_cltc) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cltc] using (Nominal.classEqRefl (syn_cltc)))
  have p0001 :=
    @g_lecex
  have p0002 :=
    @g_idex
  have p0003 :=
    @g_difex (syn_clec) (syn_cid) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cltc) (syn_cdif (syn_clec) (syn_cid)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_ncex
    (A : Class) :
    Nominal.NPrf (.classMem (syn_cnc A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc A)))
  have p0001 :=
    @g_enex
  have p0002 :=
    @g_ecexg A (syn_cvv) (syn_cen)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cnc A) (syn_cec A (syn_cen)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_nulnnc
     :
    Nominal.NPrf (.neg (.classMem (syn_c0) (syn_cncs))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_eqid (syn_c0)
  have p0001 :=
    @g_dmen
  have p0002 :=
    @g_elqsn0 (syn_cvv) (syn_c0) (syn_cen)
  have p0003 :=
    @g_mpan (.classEq (syn_cdm (syn_cen)) (syn_cvv)) (.classMem (syn_c0) (syn_cqs (syn_cvv) (syn_cen))) (syn_wne (syn_c0) (syn_c0)) p0001 p0002
  have p0004 :=
    (by simpa [syn_cncs] using (Nominal.classEqRefl (syn_cncs)))
  have p0005 :=
    @g_eleq2s (syn_wne (syn_c0) (syn_c0)) (syn_c0) (syn_cqs (syn_cvv) (syn_cen)) (syn_cncs) p0003 p0004
  have p0006 :=
    @g_necon2bi (.classMem (syn_c0) (syn_cncs)) (syn_c0) (syn_c0) p0005
  have p0007 :=
    Nominal.mp p0000 p0006
  exact p0007

#print axioms g_nulnnc

end NFChoice.DirectNominalPrf.WPPReplay
