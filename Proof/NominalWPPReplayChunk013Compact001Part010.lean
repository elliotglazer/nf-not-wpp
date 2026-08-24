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
import NominalWPPReplayChunk013Compact001Part009

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

noncomputable def g_f1opprod
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1o F A C) (syn_wf1o G B D)) (syn_wf1o (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fnpprod A B F G
  have p0001 :=
    @g_fnpprod C D (syn_ccnv F) (syn_ccnv G)
  have p0002 :=
    @g_cnvpprod F G
  have p0003 :=
    @g_fneq1i (syn_cxp C D) (syn_ccnv (syn_cpprod F G)) (syn_cpprod (syn_ccnv F) (syn_ccnv G)) p0002
  have p0004 :=
    @g_sylibr (syn_wa (syn_wfn (syn_ccnv F) C) (syn_wfn (syn_ccnv G) D)) (syn_wfn (syn_cpprod (syn_ccnv F) (syn_ccnv G)) (syn_cxp C D)) (syn_wfn (syn_ccnv (syn_cpprod F G)) (syn_cxp C D)) p0001 p0003
  have p0005 :=
    @g_anim12i (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_wfn (syn_cpprod F G) (syn_cxp A B)) (syn_wa (syn_wfn (syn_ccnv F) C) (syn_wfn (syn_ccnv G) D)) (syn_wfn (syn_ccnv (syn_cpprod F G)) (syn_cxp C D)) p0000 p0004
  have p0006 :=
    @g_an4s (syn_wfn F A) (syn_wfn G B) (syn_wfn (syn_ccnv F) C) (syn_wfn (syn_ccnv G) D) (syn_wa (syn_wfn (syn_cpprod F G) (syn_cxp A B)) (syn_wfn (syn_ccnv (syn_cpprod F G)) (syn_cxp C D))) p0005
  have p0007 :=
    @g_dff1o4 A C F
  have p0008 :=
    @g_dff1o4 B D G
  have p0009 :=
    @g_anbi12i (syn_wf1o F A C) (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) C)) (syn_wf1o G B D) (syn_wa (syn_wfn G B) (syn_wfn (syn_ccnv G) D)) p0007 p0008
  have p0010 :=
    @g_dff1o4 (syn_cxp A B) (syn_cxp C D) (syn_cpprod F G)
  have p0011 :=
    @g_n_3imtr4i (syn_wa (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) C)) (syn_wa (syn_wfn G B) (syn_wfn (syn_ccnv G) D))) (syn_wa (syn_wfn (syn_cpprod F G) (syn_cxp A B)) (syn_wfn (syn_ccnv (syn_cpprod F G)) (syn_cxp C D))) (syn_wa (syn_wf1o F A C) (syn_wf1o G B D)) (syn_wf1o (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D)) p0006 p0009 p0010
  exact p0011

noncomputable def g_ovcross
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classEq (syn_co A (syn_ccross) B) (syn_cxp A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
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
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cxp A (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex A V
  have p0001 :=
    @g_elex B W
  have p0002 :=
    @g_xpexg A B (syn_cvv) (syn_cvv)
  have p0003 :=
    @g_xpeq1 (.cv x) A (.cv y)
  have p0004 :=
    @g_xpeq2 (.cv y) B A
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cross x y dv_cache_0001
  have p0006 :=
    @g_ovmpt2g x y A B (syn_cvv) (syn_cvv) (syn_cxp (.cv x) (.cv y)) (syn_cxp A B) (syn_ccross) (syn_cxp A (.cv y)) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0001 p0003 p0004 p0005
  have p0007 :=
    @g_mpd3an3 (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cxp A B) (syn_cvv)) (.classEq (syn_co A (syn_ccross) B) (syn_cxp A B)) p0002 p0006
  have p0008 :=
    @g_syl2an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classEq (syn_co A (syn_ccross) B) (syn_cxp A B)) (.classMem B W) p0000 p0001 p0007
  exact p0008

noncomputable def g_fncross
     :
    Nominal.NPrf (syn_wfn (syn_ccross) (syn_cvv)) := by
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
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cross x y dv_cache_0001
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_vex y
  have p0003 :=
    @g_xpex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @g_fnmpt2i x y (syn_cvv) (syn_cvv) (syn_cxp (.cv x) (.cv y)) (syn_ccross) dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0001 p0000 p0003
  have p0005 :=
    @g_xpvv
  have p0006 :=
    @g_fneq2i (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ccross) p0005
  have p0007 :=
    @g_mpbi (syn_wfn (syn_ccross) (syn_cxp (syn_cvv) (syn_cvv))) (syn_wfn (syn_ccross) (syn_cvv)) p0004 p0006
  exact p0007

noncomputable def g_brcrossg
    (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (syn_wbr (syn_cop A B) (syn_ccross) C) (.classEq C (syn_cxp A B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_eqcom C (syn_co A (syn_ccross) B)
  have p0001 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co A (syn_ccross) B)))
  have p0002 :=
    @g_eqeq1i (syn_co A (syn_ccross) B) (syn_cfv (syn_ccross) (syn_cop A B)) C p0001
  have p0003 :=
    @g_bitri (.classEq C (syn_co A (syn_ccross) B)) (.classEq (syn_co A (syn_ccross) B) C) (.classEq (syn_cfv (syn_ccross) (syn_cop A B)) C) p0000 p0002
  have p0004 :=
    @g_fncross
  have p0005 :=
    @g_opexg A B V W
  have p0006 :=
    @g_fnbrfvb (syn_cvv) (syn_cop A B) C (syn_ccross)
  have p0007 :=
    @g_sylancr (syn_wa (.classMem A V) (.classMem B W)) (syn_wfn (syn_ccross) (syn_cvv)) (.classMem (syn_cop A B) (syn_cvv)) (syn_wb (.classEq (syn_cfv (syn_ccross) (syn_cop A B)) C) (syn_wbr (syn_cop A B) (syn_ccross) C)) p0004 p0005 p0006
  have p0008 :=
    @g_syl5bb (.classEq C (syn_co A (syn_ccross) B)) (.classEq (syn_cfv (syn_ccross) (syn_cop A B)) C) (syn_wa (.classMem A V) (.classMem B W)) (syn_wbr (syn_cop A B) (syn_ccross) C) p0003 p0007
  have p0009 :=
    @g_ovcross A B V W
  have p0010 :=
    @g_eqeq2d (syn_wa (.classMem A V) (.classMem B W)) (syn_co A (syn_ccross) B) (syn_cxp A B) C p0009
  have p0011 :=
    @g_bitr3d (syn_wa (.classMem A V) (.classMem B W)) (.classEq C (syn_co A (syn_ccross) B)) (syn_wbr (syn_cop A B) (syn_ccross) C) (.classEq C (syn_cxp A B)) p0008 p0010
  exact p0011

noncomputable def g_brcross
    (A : Class) (B : Class) (C : Class) (hyp_brcross_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_brcross_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_cop A B) (syn_ccross) C) (.classEq C (syn_cxp A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_brcrossg A B C (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (syn_wbr (syn_cop A B) (syn_ccross) C) (.classEq C (syn_cxp A B))) hyp_brcross_1 hyp_brcross_2 p0000
  exact p0001

noncomputable def g_crossex
     :
    Nominal.NPrf (.classMem (syn_ccross) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : b ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0005 : a ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_z, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_x, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((syn_cxp (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0020 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cross x y dv_cache_0001
  have p0001 :=
    @g_rexcom (.classEq (.cv z) (syn_cop (.cv a) (.cv b))) a b (.cv x) (.cv y) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_elxp2 a b (.cv z) (.cv x) (.cv y) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0002 dv_cache_0003 dv_cache_0008 dv_cache_0004
  have p0003 :=
    @g_elin (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))
  have p0004 :=
    @g_snex (.cv z)
  have p0005 :=
    @g_otelins2 (syn_csn (.cv b)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) (syn_cins2 (syn_csset)) p0004
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_otelins2 (syn_csn (.cv b)) (.cv x) (.cv y) (syn_csset) p0006
  have p0008 :=
    @g_vex b
  have p0009 :=
    @g_vex y
  have p0010 :=
    @g_opelssetsn (.cv b) (.cv y) p0008 p0009
  have p0011_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv b)) (.cv y)) (syn_csset)) (.objMem b y)) :=
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
      p0010
  have p0011 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv b)) (.cv y)) (syn_csset)) (.objMem b y) p0005 p0007 p0011_e02_recanon
  have p0012 :=
    @g_oqelins4 (syn_csn (.cv b)) (syn_csn (.cv z)) (.cv x) (.cv y) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)) p0009
  have p0013 :=
    @g_elin (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))
  have p0014 :=
    @g_snex (.cv b)
  have p0015 :=
    @g_otelins2 (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_cins2 (syn_csset)) p0014
  have p0016 :=
    @g_otelins2 (syn_csn (.cv a)) (syn_csn (.cv z)) (.cv x) (syn_csset) p0004
  have p0017 :=
    @g_vex a
  have p0018 :=
    @g_opelssetsn (.cv a) (.cv x) p0017 p0006
  have p0019_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv a)) (.cv x)) (syn_csset)) (.objMem a x)) :=
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
      p0018
  have p0019 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv a)) (.cv x)) (syn_csset)) (.objMem a x) p0015 p0016 p0019_e02_recanon
  have p0020 :=
    @g_oqelins4 (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_csn (.cv z)) (.cv x) (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))) p0006
  have p0021 :=
    @g_vex z
  have p0022 :=
    @g_otsnelsi3 (.cv a) (.cv b) (.cv z) (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))) p0017 p0008 p0021
  have p0023 :=
    @g_elin (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))
  have p0024 :=
    @g_otelins2 (.cv a) (.cv b) (.cv z) (syn_ccnv (syn_c1st)) p0008
  have p0025 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_ccnv (syn_c1st)) (.cv z))))
  have p0026 :=
    @g_brcnv (.cv a) (.cv z) (syn_c1st)
  have p0027 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins2 (syn_ccnv (syn_c1st)))) (.classMem (syn_cop (.cv a) (.cv z)) (syn_ccnv (syn_c1st))) (syn_wbr (.cv a) (syn_ccnv (syn_c1st)) (.cv z)) (syn_wbr (.cv z) (syn_c1st) (.cv a)) p0024 p0025 p0026
  have p0028 :=
    @g_opelxp (.cv a) (syn_cop (.cv b) (.cv z)) (syn_cvv) (syn_ccnv (syn_c2nd))
  have p0029 :=
    @g_mpbiran (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))) (.classMem (.cv a) (syn_cvv)) (.classMem (syn_cop (.cv b) (.cv z)) (syn_ccnv (syn_c2nd))) p0017 p0028
  have p0030 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (.cv z))))
  have p0031 :=
    @g_brcnv (.cv b) (.cv z) (syn_c2nd)
  have p0032 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))) (.classMem (syn_cop (.cv b) (.cv z)) (syn_ccnv (syn_c2nd))) (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (.cv z)) (syn_wbr (.cv z) (syn_c2nd) (.cv b)) p0029 p0030 p0031
  have p0033 :=
    @g_anbi12i (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins2 (syn_ccnv (syn_c1st)))) (syn_wbr (.cv z) (syn_c1st) (.cv a)) (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))) (syn_wbr (.cv z) (syn_c2nd) (.cv b)) p0027 p0032
  have p0034 :=
    @g_op1st2nd (.cv a) (.cv b) (.cv z) p0017 p0008
  have p0035 :=
    @g_n_3bitri (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))) (syn_wa (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins2 (syn_ccnv (syn_c1st)))) (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))) (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv a)) (syn_wbr (.cv z) (syn_c2nd) (.cv b))) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))) p0023 p0033 p0034
  have p0036 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_csn (.cv z)))) (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))) (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))) p0020 p0022 p0035
  have p0037 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem a x) (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))) p0019 p0036
  have p0038 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))) (syn_wa (.objMem a x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) p0013 p0037
  have p0039 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))) (syn_wa (.objMem a x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) a p0038
  have p0040 :=
    @g_elima1c a (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) dv_cache_0009 dv_cache_0010
  have p0041 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))))
  have p0042_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) (syn_wex a (syn_wa (.objMem a x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0041
  have p0042 :=
    @g_n_3bitr4i (syn_wex a (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))))) (syn_wex a (syn_wa (.objMem a x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) p0039 p0040 p0042_e02_recanon
  have p0043 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) p0012 p0042
  have p0044 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem b y) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) p0011 p0043
  have p0045 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))) (syn_wa (.objMem b y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))) p0003 p0044
  have p0046 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))) (syn_wa (.objMem b y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))) b p0045
  have p0047 :=
    @g_elima1c b (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) dv_cache_0011 dv_cache_0012
  have p0048 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex b (.cv y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))))
  have p0049_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex b (.cv y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))) (syn_wex b (syn_wa (.objMem b y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0048
  have p0049 :=
    @g_n_3bitr4i (syn_wex b (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))))) (syn_wex b (syn_wa (.objMem b y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c))) (syn_wrex b (.cv y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))) p0046 p0047 p0049_e02_recanon
  have p0050 :=
    @g_n_3bitr4ri (syn_wrex a (.cv x) (syn_wrex b (.cv y) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))) (syn_wrex b (.cv y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))) (.classMem (.cv z) (syn_cxp (.cv x) (.cv y))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c))) p0001 p0002 p0049
  have p0051 :=
    @g_releqmpt2 x y z (syn_cvv) (syn_cvv) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c)) (syn_cxp (.cv x) (.cv y)) dv_cache_0013 dv_cache_0014 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0001 dv_cache_0019 dv_cache_0020 p0050
  have p0052 :=
    @g_eqtr4i (syn_ccross) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cxp (.cv x) (.cv y))) (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c)))) (syn_c1c))) p0000 p0051
  have p0053 :=
    @g_vvex
  have p0054 :=
    @g_vvex
  have p0055 :=
    @g_ssetex
  have p0056 :=
    @g_ins2ex (syn_csset) p0055
  have p0057 :=
    @g_ins2ex (syn_cins2 (syn_csset)) p0056
  have p0058 :=
    @g_n_1stex
  have p0059 :=
    @g_cnvex (syn_c1st) p0058
  have p0060 :=
    @g_ins2ex (syn_ccnv (syn_c1st)) p0059
  have p0061 :=
    @g_vvex
  have p0062 :=
    @g_n_2ndex
  have p0063 :=
    @g_cnvex (syn_c2nd) p0062
  have p0064 :=
    @g_xpex (syn_cvv) (syn_ccnv (syn_c2nd)) p0061 p0063
  have p0065 :=
    @g_inex (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))) p0060 p0064
  have p0066 :=
    @g_si3ex (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))) p0065
  have p0067 :=
    @g_ins4ex (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))) p0066
  have p0068 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))) p0057 p0067
  have p0069 :=
    @g_n_1cex
  have p0070 :=
    @g_imaex (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c) p0068 p0069
  have p0071 :=
    @g_ins4ex (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)) p0070
  have p0072 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))) p0057 p0071
  have p0073 :=
    @g_n_1cex
  have p0074 :=
    @g_imaex (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c) p0072 p0073
  have p0075 :=
    @g_mpt2exlem (syn_cvv) (syn_cvv) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c)) p0053 p0054 p0074
  have p0076 :=
    @g_eqeltri (syn_ccross) (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c)))) (syn_c1c))) (syn_cvv) p0052 p0075
  exact p0076

noncomputable def g_pw1fnval
    (A : Class) (hyp_pw1fnval_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cpw1fn) (syn_csn A)) (syn_cpw1 A)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have dv_cache_0001 : x ∉ ((syn_csn A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cpw1 A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_snel1c A hyp_pw1fnval_1
  have p0001 :=
    @g_unieq (.cv x) (syn_csn A)
  have p0002 :=
    @g_unisn A hyp_pw1fnval_1
  have p0003 :=
    @g_syl6eq (.classEq (.cv x) (syn_csn A)) (syn_cuni (.cv x)) (syn_cuni (syn_csn A)) A p0001 p0002
  have p0004 :=
    @g_pw1eq (syn_cuni (.cv x)) A
  have p0005 :=
    @g_syl (.classEq (.cv x) (syn_csn A)) (.classEq (syn_cuni (.cv x)) A) (.classEq (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1 A)) p0003 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw1fn x
  have p0007 :=
    @g_pw1ex A hyp_pw1fnval_1
  have p0008 :=
    @g_fvmpt x (syn_csn A) (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1 A) (syn_c1c) (syn_cpw1fn) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0005 p0006 p0007
  have p0009 :=
    Nominal.mp p0000 p0008
  exact p0009

#print axioms g_pw1fnval

end NFChoice.DirectNominalPrf.WPPReplay
