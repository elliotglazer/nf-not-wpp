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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk010Compact001Part034

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

noncomputable def g_nfop
    (x : Var) (A : Class) (B : Class) (hyp_nfop_1 : Nominal.NPrf (syn_wnfc x A)) (hyp_nfop_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnfc x (syn_cop A B)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : z ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0006 : x ∉ ((Wff.classEq (.cv z) (syn_cphi (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op z w A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_nfv (.classEq (.cv z) (syn_cphi (.cv w))) x dv_cache_0006
  have p0002 :=
    @g_nfrex (.classEq (.cv z) (syn_cphi (.cv w))) x w A hyp_nfop_1 p0001
  have p0003 :=
    @g_nfab (syn_wrex w A (.classEq (.cv z) (syn_cphi (.cv w)))) x z p0002
  have p0004 :=
    @g_nfv (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c)))) x dv_cache_0007
  have p0005 :=
    @g_nfrex (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c)))) x w B hyp_nfop_2 p0004
  have p0006 :=
    @g_nfab (syn_wrex w B (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c))))) x z p0005
  have p0007 :=
    @g_nfun x (.cab z (syn_wrex w A (.classEq (.cv z) (syn_cphi (.cv w))))) (.cab z (syn_wrex w B (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c)))))) p0003 p0006
  have p0008 :=
    @g_nfcxfr x (syn_cop A B) (syn_cun (.cab z (syn_wrex w A (.classEq (.cv z) (syn_cphi (.cv w))))) (.cab z (syn_wrex w B (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c))))))) p0000 p0007
  exact p0008

noncomputable def g_nfopd
    (ph : Wff) (x : Var) (A : Class) (B : Class) (hyp_nfopd_1 : Nominal.NPrf (.imp ph (syn_wnfc x A))) (hyp_nfopd_2 : Nominal.NPrf (.imp ph (syn_wnfc x B))) :
    Nominal.NPrf (.imp ph (syn_wnfc x (syn_cop A B))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nfaba1 (.classMem (.cv z) A) x z
  have p0001 :=
    @g_nfaba1 (.classMem (.cv z) B) x z
  have p0002 :=
    @g_nfop x (.cab z (.all x (.classMem (.cv z) A))) (.cab z (.all x (.classMem (.cv z) B))) p0000 p0001
  have p0003 :=
    @g_nfnfc1 x A
  have p0004 :=
    @g_nfnfc1 x B
  have p0005 :=
    @g_nfan (syn_wnfc x A) (syn_wnfc x B) x p0003 p0004
  have p0006 :=
    @g_abidnf x z A dv_cache_0001 dv_cache_0002
  have p0007 :=
    @g_adantr (syn_wnfc x A) (.classEq (.cab z (.all x (.classMem (.cv z) A))) A) (syn_wnfc x B) p0006
  have p0008 :=
    @g_abidnf x z B dv_cache_0003 dv_cache_0002
  have p0009 :=
    @g_adantl (syn_wnfc x B) (.classEq (.cab z (.all x (.classMem (.cv z) B))) B) (syn_wnfc x A) p0008
  have p0010 :=
    @g_opeq12d (syn_wa (syn_wnfc x A) (syn_wnfc x B)) (.cab z (.all x (.classMem (.cv z) A))) A (.cab z (.all x (.classMem (.cv z) B))) B p0007 p0009
  have p0011 :=
    @g_nfceqdf (syn_wa (syn_wnfc x A) (syn_wnfc x B)) x (syn_cop (.cab z (.all x (.classMem (.cv z) A))) (.cab z (.all x (.classMem (.cv z) B)))) (syn_cop A B) p0005 p0010
  have p0012 :=
    @g_syl2anc ph (syn_wnfc x A) (syn_wnfc x B) (syn_wb (syn_wnfc x (syn_cop (.cab z (.all x (.classMem (.cv z) A))) (.cab z (.all x (.classMem (.cv z) B))))) (syn_wnfc x (syn_cop A B))) hyp_nfopd_1 hyp_nfopd_2 p0011
  have p0013 :=
    @g_mpbii ph (syn_wnfc x (syn_cop (.cab z (.all x (.classMem (.cv z) A))) (.cab z (.all x (.classMem (.cv z) B))))) (syn_wnfc x (syn_cop A B)) p0002 p0012
  exact p0013

noncomputable def g_eqvinop
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) (hyp_eqvinop_1 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_eqvinop_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classEq A (syn_cop B C)) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cop (.cv x) C))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, (Ne.symm dv_x_y), dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq A (syn_cop B C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_opth (.cv x) (.cv y) B C
  have p0001 :=
    @g_ancom (.classEq (.cv x) B) (.classEq (.cv y) C)
  have p0002 :=
    @g_bitri (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C)) (syn_wa (.classEq (.cv x) B) (.classEq (.cv y) C)) (syn_wa (.classEq (.cv y) C) (.classEq (.cv x) B)) p0000 p0001
  have p0003 :=
    @g_anbi2i (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C)) (syn_wa (.classEq (.cv y) C) (.classEq (.cv x) B)) (.classEq A (syn_cop (.cv x) (.cv y))) p0002
  have p0004 :=
    @g_an13 (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (.cv y) C) (.classEq (.cv x) B)
  have p0005 :=
    @g_bitri (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C))) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (.classEq (.cv y) C) (.classEq (.cv x) B))) (syn_wa (.classEq (.cv x) B) (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C))) (syn_wa (.classEq (.cv x) B) (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y))))) y p0005
  have p0007 :=
    @g_n_19_42v (.classEq (.cv x) B) (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y)))) y dv_cache_0001
  have p0008 :=
    @g_opeq2 (.cv y) C (.cv x)
  have p0009 :=
    @g_eqeq2d (.classEq (.cv y) C) (syn_cop (.cv x) (.cv y)) (syn_cop (.cv x) C) A p0008
  have p0010 :=
    @g_ceqsexv (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq A (syn_cop (.cv x) C)) y C dv_cache_0002 dv_cache_0003 hyp_eqvinop_2 p0009
  have p0011 :=
    @g_anbi2i (syn_wex y (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y))))) (.classEq A (syn_cop (.cv x) C)) (.classEq (.cv x) B) p0010
  have p0012 :=
    @g_n_3bitri (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C)))) (syn_wex y (syn_wa (.classEq (.cv x) B) (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y)))))) (syn_wa (.classEq (.cv x) B) (syn_wex y (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y)))))) (syn_wa (.classEq (.cv x) B) (.classEq A (syn_cop (.cv x) C))) p0006 p0007 p0011
  have p0013 :=
    @g_exbii (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C)))) (syn_wa (.classEq (.cv x) B) (.classEq A (syn_cop (.cv x) C))) x p0012
  have p0014 :=
    @g_opeq1 (.cv x) B C
  have p0015 :=
    @g_eqeq2d (.classEq (.cv x) B) (syn_cop (.cv x) C) (syn_cop B C) A p0014
  have p0016 :=
    @g_ceqsexv (.classEq A (syn_cop (.cv x) C)) (.classEq A (syn_cop B C)) x B dv_cache_0004 dv_cache_0005 hyp_eqvinop_1 p0015
  have p0017 :=
    @g_bitr2i (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C))))) (syn_wex x (syn_wa (.classEq (.cv x) B) (.classEq A (syn_cop (.cv x) C)))) (.classEq A (syn_cop B C)) p0013 p0016
  exact p0017

noncomputable def g_copsexg
    (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    Nominal.NPrf (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : z ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0008 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0010 : y ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0011 : x ∉ ((Wff.classEq A (syn_cop (.cv z) (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classEq A (syn_cop (.cv z) (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, fresh_y_ne_z, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Wff.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((Wff.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_eqvinop z w A (.cv x) (.cv y) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0001
  have p0003 :=
    @g_n_19_8a (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph) y
  have p0004 :=
    @g_n_19_8a (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)) x
  have p0005 :=
    @g_syl (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph) (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)) (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))) p0003 p0004
  have p0006 :=
    @g_ex (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))) p0005
  have p0007 :=
    @g_opth (.cv z) (.cv w) (.cv x) (.cv y)
  have p0008_e00_recanon : Nominal.NPrf (syn_wb (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) (syn_wa (.objEq z x) (.objEq w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0008 :=
    @g_anbi1i (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) (syn_wa (.objEq z x) (.objEq w y)) ph p0008_e00_recanon
  have p0009 :=
    @g_n_2exbii (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph) (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph) x y p0008
  have p0010 :=
    @g_nfe1 (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) x
  have p0011 :=
    @g_nfae y x y
  have p0012 :=
    @g_anass (.objEq z x) (.objEq w y) ph
  have p0013 :=
    @g_n_19_8a (syn_wa (.objEq w y) ph) y
  have p0014 :=
    @g_a1i (.imp (syn_wa (.objEq w y) ph) (syn_wex y (syn_wa (.objEq w y) ph))) (.all y (.objEq y x)) p0013
  have p0015 :=
    @g_anim2d (.all y (.objEq y x)) (syn_wa (.objEq w y) ph) (syn_wex y (syn_wa (.objEq w y) ph)) (.objEq z x) p0014
  have p0016 :=
    @g_syl5bi (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph) (syn_wa (.objEq z x) (syn_wa (.objEq w y) ph)) (.all y (.objEq y x)) (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) p0012 p0015
  have p0017 :=
    @g_eximd (.all y (.objEq y x)) (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph) (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) y p0011 p0016
  have p0018 :=
    @g_biidd (.all y (.objEq y x)) (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))
  have p0019 :=
    @g_drex1 (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) y x p0018
  have p0020 :=
    @g_sylibd (.all y (.objEq y x)) (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)) (syn_wex y (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) p0017 p0019
  have p0021 :=
    @g_exbii (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph) (syn_wa (.objEq z x) (syn_wa (.objEq w y) ph)) y p0012
  have p0022 :=
    @g_n_19_40 (.objEq z x) (syn_wa (.objEq w y) ph) y
  have p0023 :=
    @g_nfnae y x y
  have p0024 :=
    @g_dveeq2 y x z dv_cache_0008
  have p0025 :=
    @g_nfd (.neg (.all y (.objEq y x))) (.objEq z x) y p0023 p0024
  have p0026 :=
    @g_n_19_9d (.objEq z x) (.neg (.all y (.objEq y x))) y p0025
  have p0027 :=
    @g_anim1d (.neg (.all y (.objEq y x))) (syn_wex y (.objEq z x)) (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)) p0026
  have p0028 :=
    @g_syl5 (syn_wex y (syn_wa (.objEq z x) (syn_wa (.objEq w y) ph))) (syn_wa (syn_wex y (.objEq z x)) (syn_wex y (syn_wa (.objEq w y) ph))) (.neg (.all y (.objEq y x))) (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) p0022 p0027
  have p0029 :=
    @g_syl5bi (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)) (syn_wex y (syn_wa (.objEq z x) (syn_wa (.objEq w y) ph))) (.neg (.all y (.objEq y x))) (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) p0021 p0028
  have p0030 :=
    @g_n_19_8a (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) x
  have p0031 :=
    @g_syl6 (.neg (.all y (.objEq y x))) (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)) (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) p0029 p0030
  have p0032 :=
    @g_pm2_61i (.all y (.objEq y x)) (.imp (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)) (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))))) p0020 p0031
  have p0033 :=
    @g_exlimi (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)) (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) x p0010 p0032
  have p0034 :=
    @g_euequ1 x z dv_cache_0009
  have p0035 :=
    @g_equcom x z
  have p0036 :=
    @g_eubii (.objEq x z) (.objEq z x) x p0035
  have p0037 :=
    @g_mpbi (syn_weu x (.objEq x z)) (syn_weu x (.objEq z x)) p0034 p0036
  have p0038 :=
    @g_eupick (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)) x
  have p0039 :=
    @g_mpan (syn_weu x (.objEq z x)) (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) (.imp (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) p0037 p0038
  have p0040 :=
    @g_com12 (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)) p0039
  have p0041 :=
    @g_euequ1 y w dv_cache_0010
  have p0042 :=
    @g_equcom y w
  have p0043 :=
    @g_eubii (.objEq y w) (.objEq w y) y p0042
  have p0044 :=
    @g_mpbi (syn_weu y (.objEq y w)) (syn_weu y (.objEq w y)) p0041 p0043
  have p0045 :=
    @g_eupick (.objEq w y) ph y
  have p0046 :=
    @g_mpan (syn_weu y (.objEq w y)) (syn_wex y (syn_wa (.objEq w y) ph)) (.imp (.objEq w y) ph) p0044 p0045
  have p0047 :=
    @g_com12 (syn_wex y (syn_wa (.objEq w y) ph)) (.objEq w y) ph p0046
  have p0048 :=
    @g_sylan9 (.objEq z x) (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) (syn_wex y (syn_wa (.objEq w y) ph)) (.objEq w y) ph p0040 p0047
  have p0049 :=
    @g_syl5 (syn_wex x (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph))) (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) (syn_wa (.objEq z x) (.objEq w y)) ph p0033 p0048
  have p0050 :=
    @g_syl5bi (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))) (syn_wex x (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph))) (syn_wa (.objEq z x) (.objEq w y)) ph p0009 p0049
  have p0051_e00_recanon : Nominal.NPrf (syn_wb (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) (syn_wa (.objEq z x) (.objEq w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0051 :=
    @g_sylbi (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) (syn_wa (.objEq z x) (.objEq w y)) (.imp (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))) ph) p0051_e00_recanon p0050
  have p0052 :=
    @g_impbid (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))) p0006 p0051
  have p0053 :=
    @g_eqeq1 A (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))
  have p0054 :=
    @g_anbi1d (.classEq A (syn_cop (.cv z) (.cv w))) (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph p0053
  have p0055 :=
    @g_n_2exbidv (.classEq A (syn_cop (.cv z) (.cv w))) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph) (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph) x y dv_cache_0011 dv_cache_0012 p0054
  have p0056 :=
    @g_bibi2d (.classEq A (syn_cop (.cv z) (.cv w))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))) (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))) ph p0055
  have p0057 :=
    @g_imbi12d (.classEq A (syn_cop (.cv z) (.cv w))) (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)))) p0053 p0056
  have p0058 :=
    @g_mpbiri (.classEq A (syn_cop (.cv z) (.cv w))) (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))))) (.imp (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))))) p0052 p0057
  have p0059 :=
    @g_adantr (.classEq A (syn_cop (.cv z) (.cv w))) (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))))) (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) p0058
  have p0060 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cop (.cv z) (.cv w))) (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y)))) (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))))) z w dv_cache_0013 dv_cache_0014 p0059
  have p0061 :=
    @g_sylbi (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w))) (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y)))))) (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))))) p0002 p0060
  have p0062 :=
    @g_pm2_43i (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))) p0061
  exact p0062

noncomputable def g_copsex2g
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class) (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y) (hyp_copsex2g_1 : Nominal.NPrf (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cop A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cop A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elisset x A V dv_cache_0001
  have p0001 :=
    @g_elisset y B W dv_cache_0002
  have p0002 :=
    @g_eeanv (.classEq (.cv x) A) (.classEq (.cv y) B) x y dv_cache_0003 dv_cache_0004
  have p0003 :=
    @g_nfe1 (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)) x
  have p0004 :=
    @g_nfv ps x dv_cache_0005
  have p0005 :=
    @g_nfbi (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps x p0003 p0004
  have p0006 :=
    @g_nfe1 (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph) y
  have p0007 :=
    @g_nfex (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)) y x p0006
  have p0008 :=
    @g_nfv ps y dv_cache_0006
  have p0009 :=
    @g_nfbi (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps y p0007 p0008
  have p0010 :=
    @g_opeq12 (.cv x) A (.cv y) B
  have p0011 :=
    @g_copsexg ph x y (syn_cop A B) dv_cache_0007 dv_cache_0008
  have p0012 :=
    @g_eqcoms (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)))) (syn_cop A B) (syn_cop (.cv x) (.cv y)) p0011
  have p0013 :=
    @g_syl (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B)) (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)))) p0010 p0012
  have p0014 :=
    @g_bitr3d (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps p0013 hyp_copsex2g_1
  have p0015 :=
    @g_exlimi (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps) y p0009 p0014
  have p0016 :=
    @g_exlimi (syn_wex y (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))) (syn_wb (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps) x p0005 p0015
  have p0017 :=
    @g_sylbir (syn_wa (syn_wex x (.classEq (.cv x) A)) (syn_wex y (.classEq (.cv y) B))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)))) (syn_wb (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps) p0002 p0016
  have p0018 :=
    @g_syl2an (.classMem A V) (syn_wex x (.classEq (.cv x) A)) (syn_wex y (.classEq (.cv y) B)) (syn_wb (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps) (.classMem B W) p0000 p0001 p0017
  exact p0018

noncomputable def g_eqop
    (z : Var) (t : Var) (A : Class) (B : Class) (C : Class) (dv_A_t : t ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_t : t ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_t : t ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_t_z : t ≠ z) :
    Nominal.NPrf (syn_wb (.classEq A (syn_cop B C)) (.all z (syn_wb (.classMem (.cv z) A) (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ ({t} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have dv_cache_0001 : z ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cop B C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_z, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show z ≠ t from (by exact Ne.symm dv_t_z))
  have p0000 :=
    @g_dfcleq z A (syn_cop B C) dv_cache_0001 dv_cache_0002
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op z t B C dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @g_eleq2i (syn_cop B C) (syn_cun (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t))))) (.cab z (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))) (.cv z) p0001
  have p0003 :=
    @g_elun (.cv z) (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t))))) (.cab z (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))
  have p0004 :=
    @g_bitri (.classMem (.cv z) (syn_cop B C)) (.classMem (.cv z) (syn_cun (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t))))) (.cab z (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))))) (syn_wo (.classMem (.cv z) (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))))) (.classMem (.cv z) (.cab z (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))))) p0002 p0003
  have p0005 :=
    @g_abid (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) z
  have p0006 :=
    @g_abid (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))) z
  have p0007 :=
    @g_orbi12i (.classMem (.cv z) (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))))) (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (.classMem (.cv z) (.cab z (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))) (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))) p0005 p0006
  have p0008 :=
    @g_bitri (.classMem (.cv z) (syn_cop B C)) (syn_wo (.classMem (.cv z) (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))))) (.classMem (.cv z) (.cab z (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))))) (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))) p0004 p0007
  have p0009 :=
    @g_bibi2i (.classMem (.cv z) (syn_cop B C)) (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))) (.classMem (.cv z) A) p0008
  have p0010 :=
    @g_albii (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) (syn_cop B C))) (syn_wb (.classMem (.cv z) A) (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))) z p0009
  have p0011 :=
    @g_bitri (.classEq A (syn_cop B C)) (.all z (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) (syn_cop B C)))) (.all z (syn_wb (.classMem (.cv z) A) (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))))) p0000 p0010
  exact p0011

noncomputable def g_mosubopt
    (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (.all y (.all z (syn_wmo x ph))) (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A (syn_cop (.cv y) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_x_y, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_x_y, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nfa1 (.all z (syn_wmo x ph)) y
  have p0001 :=
    @g_nfe1 (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)) y
  have p0002 :=
    @g_nfmo (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))) y x p0001
  have p0003 :=
    @g_nfa1 (syn_wmo x ph) z
  have p0004 :=
    @g_nfe1 (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph) z
  have p0005 :=
    @g_nfex (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)) z y p0004
  have p0006 :=
    @g_nfmo (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))) z x p0005
  have p0007 :=
    @g_copsexg ph y z A dv_cache_0001 dv_cache_0002
  have p0008 :=
    @g_mobidv (.classEq A (syn_cop (.cv y) (.cv z))) ph (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))) x dv_cache_0003 p0007
  have p0009 :=
    @g_biimpcd (.classEq A (syn_cop (.cv y) (.cv z))) (syn_wmo x ph) (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))) p0008
  have p0010 :=
    @g_sps (syn_wmo x ph) (.imp (.classEq A (syn_cop (.cv y) (.cv z))) (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))) z p0009
  have p0011 :=
    @g_exlimd (.all z (syn_wmo x ph)) (.classEq A (syn_cop (.cv y) (.cv z))) (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))) z p0003 p0006 p0010
  have p0012 :=
    @g_sps (.all z (syn_wmo x ph)) (.imp (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z)))) (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))) y p0011
  have p0013 :=
    @g_exlimd (.all y (.all z (syn_wmo x ph))) (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z)))) (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))) y p0000 p0002 p0012
  have p0014 :=
    @g_simpl (.classEq A (syn_cop (.cv y) (.cv z))) ph
  have p0015 :=
    @g_n_2eximi (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph) (.classEq A (syn_cop (.cv y) (.cv z))) y z p0014
  have p0016 :=
    @g_exlimiv (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))) (syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z))))) x dv_cache_0004 p0015
  have p0017 :=
    @g_con3i (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))) (syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z))))) p0016
  have p0018 :=
    @g_exmo (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))) x
  have p0019 :=
    @g_ori (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))) (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))) p0018
  have p0020 :=
    @g_syl (.neg (syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z)))))) (.neg (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))) (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))) p0017 p0019
  have p0021 :=
    @g_pm2_61d1 (.all y (.all z (syn_wmo x ph))) (syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z))))) (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))) p0013 p0020
  exact p0021

#print axioms g_mosubopt

end NFChoice.DirectNominalPrf.WPPReplay
