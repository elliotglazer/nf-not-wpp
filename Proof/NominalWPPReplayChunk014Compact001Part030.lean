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
import NominalWPPReplayChunk014Compact001Part029

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

noncomputable def g_hwcodesexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_chwcodes A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0001 :=
    @g_weex
  have p0002 :=
    @g_a1i (.classMem (syn_cwe) (syn_cvv)) (.classMem A V) p0001
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_a1i (.classMem (syn_cvv) (syn_cvv)) (.classMem A V) p0003
  have p0005 :=
    @g_pwexg A V
  have p0006 :=
    @g_jca (.classMem A V) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cpw A) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_xpexg (syn_cvv) (syn_cpw A) (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl (.classMem A V) (syn_wa (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cpw A) (syn_cvv))) (.classMem (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_jca (.classMem A V) (.classMem (syn_cwe) (syn_cvv)) (.classMem (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cvv)) p0002 p0008
  have p0010 :=
    @g_inexg (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_syl (.classMem A V) (syn_wa (.classMem (syn_cwe) (syn_cvv)) (.classMem (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cvv))) (.classMem (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_syl5eqel (.classMem A V) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cvv) p0000 p0011
  exact p0012

noncomputable def g_elhwcodes
    (A : Class) (D : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_elhwcodes_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_elhwcodes_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop R D) (syn_chwcodes A)) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wss D A))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0001 :=
    @g_eleq2i (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cop R D) p0000
  have p0002 :=
    @g_elin (syn_cop R D) (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr R (syn_cwe) D)))
  have p0004 :=
    @g_bicomi (syn_wbr R (syn_cwe) D) (.classMem (syn_cop R D) (syn_cwe)) p0003
  have p0005 :=
    @g_opelxp R D (syn_cvv) (syn_cpw A)
  have p0006 :=
    @g_mpbiran (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_cpw A))) (.classMem R (syn_cvv)) (.classMem D (syn_cpw A)) hyp_elhwcodes_1 p0005
  have p0007 :=
    @g_elpw D A hyp_elhwcodes_2
  have p0008 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_cpw A))) (.classMem D (syn_cpw A)) (syn_wss D A) p0006 p0007
  have p0009 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_cwe)) (syn_wbr R (syn_cwe) D) (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_wss D A) p0004 p0008
  have p0010 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (syn_wa (.classMem (syn_cop R D) (syn_cwe)) (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_cpw A)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wss D A)) p0002 p0009
  have p0011 :=
    @g_bitri (.classMem (syn_cop R D) (syn_chwcodes A)) (.classMem (syn_cop R D) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wss D A)) p0001 p0010
  exact p0011

noncomputable def g_brhwiso
    (v : Var) (u : Var) (A : Class) (h : Var) (dv_A_h : h ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({h} : Finset Var)
  have dv_cache_0001 : h ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact dv_h_u))
  have dv_cache_0005 : h ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ v from (by exact dv_h_v))
  have dv_cache_0006 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact dv_u_v))
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chwiso A) (.cv v))))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_hwiso v u A h dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_eleq2i (syn_chwiso A) (syn_copab u v (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) (syn_cop (.cv u) (.cv v)) p0001
  have p0003 :=
    @g_opabid (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) u v
  have p0004 :=
    @g_bitri (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwiso A)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_copab u v (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0002 p0003
  have p0005 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwiso A)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0000 p0004
  exact p0005

noncomputable def g_brhwisoany
    (v : Var) (u : Var) (A : Class) (h : Var) (dv_A_h : h ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({h} : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_h : x ≠ h := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_x : h ≠ x :=
    Ne.symm fresh_x_ne_h
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_v : y ≠ v := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_h : y ≠ h := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_y : h ≠ y :=
    Ne.symm fresh_y_ne_h
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : h ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0004 : h ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have dv_cache_0005 : h ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ y from (by exact fresh_h_ne_y))
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : h ∉ ((Wff.classEq (.cv x) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_x, dv_h_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : h ∉ ((Wff.classEq (.cv y) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_y, dv_h_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A, fresh_x_ne_v, fresh_x_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, fresh_y_not_A, fresh_y_ne_v, fresh_y_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chwiso A) (.cv v))))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_hwiso y x A h dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_eleq2i (syn_chwiso A) (syn_copab x y (syn_wa (syn_wa (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))))) (syn_cop (.cv u) (.cv v)) p0001
  have p0003 :=
    @g_vex u
  have p0004 :=
    @g_vex v
  have p0005 :=
    @g_eleq1 (.cv x) (.cv u) (syn_chwcodes A)
  have p0006 :=
    @g_anbi1d (.classEq (.cv x) (.cv u)) (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A)) p0005
  have p0007 :=
    @g_fveq2 (.cv x) (.cv u) (syn_c1st)
  have p0008 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c1st) (.cv u)) (.cv h)
  have p0009 :=
    @g_syl (.classEq (.cv x) (.cv u)) (.classEq (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv u))) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))) p0007 p0008
  have p0010 :=
    @g_fveq2 (.cv x) (.cv u) (syn_c2nd)
  have p0011 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (.cv h)
  have p0012 :=
    @g_syl (.classEq (.cv x) (.cv u)) (.classEq (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv u))) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))) p0010 p0011
  have p0013 :=
    @g_bitrd (.classEq (.cv x) (.cv u)) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))) p0009 p0012
  have p0014 :=
    @g_exbidv (.classEq (.cv x) (.cv u)) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))) h dv_cache_0007 p0013
  have p0015 :=
    @g_anbi12d (.classEq (.cv x) (.cv u)) (syn_wa (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))) p0006 p0014
  have p0016 :=
    @g_eleq1 (.cv y) (.cv v) (syn_chwcodes A)
  have p0017 :=
    @g_anbi2d (.classEq (.cv y) (.cv v)) (.classMem (.cv y) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)) p0016
  have p0018 :=
    @g_fveq2 (.cv y) (.cv v) (syn_c1st)
  have p0019 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0020 :=
    @g_syl (.classEq (.cv y) (.cv v)) (.classEq (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c1st) (.cv v))) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))) p0018 p0019
  have p0021 :=
    @g_fveq2 (.cv y) (.cv v) (syn_c2nd)
  have p0022 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0023 :=
    @g_syl (.classEq (.cv y) (.cv v)) (.classEq (syn_cfv (syn_c2nd) (.cv y)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0021 p0022
  have p0024 :=
    @g_bitrd (.classEq (.cv y) (.cv v)) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0020 p0023
  have p0025 :=
    @g_exbidv (.classEq (.cv y) (.cv v)) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) h dv_cache_0008 p0024
  have p0026 :=
    @g_anbi12d (.classEq (.cv y) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0017 p0025
  have p0027 :=
    @g_sylan9bb (.classEq (.cv x) (.cv u)) (syn_wa (syn_wa (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))))) (.classEq (.cv y) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0015 p0026
  have p0028 :=
    @g_opelopaba (syn_wa (syn_wa (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) x y (.cv u) (.cv v) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0006 p0003 p0004 p0027
  have p0029 :=
    @g_bitri (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwiso A)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_copab x y (syn_wa (syn_wa (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0002 p0028
  have p0030 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwiso A)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0000 p0029
  exact p0030

noncomputable def g_hwisosymi
    (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf (.imp (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv u))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  let g : Var := freshVar proofSupport 0
  let h : Var := freshVar proofSupport 1
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_ne_v : g ≠ v := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_g : v ≠ g :=
    Ne.symm fresh_g_ne_v
  have fresh_g_ne_u : g ≠ u := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_g : u ≠ g :=
    Ne.symm fresh_g_ne_u
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_h_ne_v : h ≠ v := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_h : v ≠ h :=
    Ne.symm fresh_h_ne_v
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_h : u ≠ h :=
    Ne.symm fresh_h_ne_u
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_g_ne_h : g ≠ h := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_h_ne_g : h ≠ g :=
    Ne.symm fresh_g_ne_h
  have dv_cache_0001 : h ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0005 : h ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0006 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0007 : g ∉ ((syn_ccnv (.cv h))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : g ∉ ((syn_wiso (syn_ccnv (.cv h)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_v, fresh_g_ne_u, fresh_g_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : h ∉ ((syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_v, fresh_h_ne_u, fresh_h_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : g ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : g ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show g ≠ v from (by exact fresh_g_ne_v))
  have dv_cache_0012 : g ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show g ≠ u from (by exact fresh_g_ne_u))
  have dv_cache_0013 : v ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show v ≠ u from (by exact Ne.symm dv_u_v))
  have p0000 :=
    @g_brhwiso v u A h dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0000
  have p0002 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0003 :=
    @g_ancom (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))
  have p0004 :=
    @g_biimpi (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) p0003
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) p0002 p0004
  have p0006 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0007 :=
    @g_isocnv (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0008 :=
    @g_vex h
  have p0009 :=
    @g_cnvex (.cv h) p0008
  have p0010 :=
    @g_isoeq1 (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_ccnv (.cv h)) (.cv g)
  have p0011 :=
    @g_spcev (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))) (syn_wiso (syn_ccnv (.cv h)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))) g (syn_ccnv (.cv h)) dv_cache_0007 dv_cache_0008 p0009 p0010
  have p0012 :=
    @g_syl (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (syn_ccnv (.cv h)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))) p0007 p0011
  have p0013 :=
    @g_exlimiv (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))) h dv_cache_0009 p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))) p0006 p0013
  have p0015 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))) p0005 p0014
  have p0016 :=
    @g_syl (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))))) p0001 p0015
  have p0017 :=
    @g_brhwiso u v A g dv_cache_0010 dv_cache_0003 dv_cache_0002 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0018 :=
    @g_biimpri (syn_wbr (.cv v) (syn_chwiso A) (.cv u)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))))) p0017
  have p0019 :=
    @g_syl (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv v) (syn_chwiso A) (.cv u)) p0016 p0018
  exact p0019

#print axioms g_hwisosymi

end NFChoice.DirectNominalPrf.WPPReplay
