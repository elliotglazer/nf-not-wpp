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
import NominalWPPReplayChunk017Compact001Part002

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

noncomputable def g_sidownsuppclndv
    (x : Var) (y : Var) (D : Class) (S : Class) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wss (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cxp D D))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ S.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : x ∉ (S).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (S).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0004 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0005 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0006 : b ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : a ∉ ((syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : b ∉ ((syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_S, fresh_b_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((syn_cxp D D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ ((syn_cxp D D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    @g_simpl (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
  have p0001 :=
    @g_simpr (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
  have p0002 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b))))
  have p0003 :=
    @g_biimpri (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) p0002
  have p0004 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)) p0001 p0003
  have p0005 :=
    @g_hndownbrclndv x y S a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0006 :=
    @g_biimpi (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) p0005
  have p0007 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) p0004 p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))))
  have p0009 :=
    @g_biimpi (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) S) p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) S) p0007 p0009
  have p0011 :=
    @g_sseldd (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)) (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) p0000 p0010
  have p0012 :=
    @g_opelxp (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_cpw1 D) (syn_cpw1 D)
  have p0013 :=
    @g_biimpi (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))) p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))) p0011 p0013
  have p0015 :=
    @g_simpl (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))
  have p0016 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0014 p0015
  have p0017 :=
    @g_snelpw1 (.cv a) D
  have p0018 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (.cv a) D)) (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) p0017
  have p0019 :=
    @g_mpbid (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (.cv a) D) p0016 p0018
  have p0020 :=
    @g_simpl (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
  have p0021 :=
    @g_simpr (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))
  have p0022 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b))))
  have p0023 :=
    @g_biimpri (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) p0022
  have p0024 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)) p0021 p0023
  have p0025 :=
    @g_hndownbrclndv x y S a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0026 :=
    @g_biimpi (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) p0025
  have p0027 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) p0024 p0026
  have p0028 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))))
  have p0029 :=
    @g_biimpi (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) S) p0028
  have p0030 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) S) p0027 p0029
  have p0031 :=
    @g_sseldd (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)) (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) p0020 p0030
  have p0032 :=
    @g_opelxp (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_cpw1 D) (syn_cpw1 D)
  have p0033 :=
    @g_biimpi (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))) p0032
  have p0034 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))) p0031 p0033
  have p0035 :=
    @g_simpr (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))
  have p0036 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (syn_csn (.cv b)) (syn_cpw1 D))) (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) p0034 p0035
  have p0037 :=
    @g_snelpw1 (.cv b) D
  have p0038 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) (.classMem (.cv b) D)) (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) p0037
  have p0039 :=
    @g_mpbid (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) (.classMem (.cv b) D) p0036 p0038
  have p0040 :=
    @g_jca (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (.classMem (.cv a) D) (.classMem (.cv b) D) p0019 p0039
  have p0041 :=
    @g_opelxp (.cv a) (.cv b) D D
  have p0042 :=
    @g_biimpri (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D)) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) p0041
  have p0043 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D)) p0040 p0042
  have p0044 :=
    @g_ex (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D)) p0043
  have p0045 :=
    @g_alrimivv (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.imp (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D))) a b dv_cache_0008 dv_cache_0009 p0044
  have p0046 :=
    @g_ssrel a b (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cxp D D) dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0047 :=
    @g_a1i (syn_wb (syn_wss (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cxp D D)) (.all a (.all b (.imp (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D)))))) (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0046
  have p0048 :=
    @g_mpbird (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wss (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cxp D D)) (.all a (.all b (.imp (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp D D))))) p0045 p0047
  exact p0048

noncomputable def g_pw1subunissclndv
    (A : Class) (S : Class) (hyp_pw1subunissclndv_1 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wss S (syn_cpw1 A)) (syn_wss (syn_cuni S) A)) := by
  let proofSupport : Finset Var := A.fv ∪ S.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (h))
  have fresh_g_not_S : g ∉ S.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have dv_cache_0001 : g ∉ (S).fv := by
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : g ∉ ((Wff.imp (syn_wss S (syn_cpw1 A)) (syn_wss (syn_cuni S) A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_S, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv g) S)
  have p0001 :=
    @g_sseq1d (.classEq (.cv g) S) (.cv g) S (syn_cpw1 A) p0000
  have p0002 :=
    @g_id (.classEq (.cv g) S)
  have p0003 :=
    @g_unieqd (.classEq (.cv g) S) (.cv g) S p0002
  have p0004 :=
    @g_sseq1d (.classEq (.cv g) S) (syn_cuni (.cv g)) (syn_cuni S) A p0003
  have p0005 :=
    @g_imbi12d (.classEq (.cv g) S) (syn_wss (.cv g) (syn_cpw1 A)) (syn_wss S (syn_cpw1 A)) (syn_wss (syn_cuni (.cv g)) A) (syn_wss (syn_cuni S) A) p0001 p0004
  have p0006 :=
    @g_pw1subuniss g A
  have p0007 :=
    @g_vtoclg (.imp (syn_wss (.cv g) (syn_cpw1 A)) (syn_wss (syn_cuni (.cv g)) A)) (.imp (syn_wss S (syn_cpw1 A)) (syn_wss (syn_cuni S) A)) g S (syn_cvv) dv_cache_0001 dv_cache_0002 p0005 p0006
  have p0008 :=
    Nominal.mp hyp_pw1subunissclndv_1 p0007
  exact p0008

noncomputable def g_hnsireversecodememndv
    (x : Var) (y : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ∉ ((syn_cpw1 A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cuni (syn_cfv (syn_c2nd) (.cv u)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cuni (syn_cfv (syn_c2nd) (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0007 : Disjoint (A).fv ((syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (A).fv ((syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab]; exact (show Disjoint ((A).fv) ((((((syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))).fv).erase y).erase x) ∪ (((({x} : Finset Var)).erase y).erase x)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((((syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))).fv).erase y).erase x) from (Disjoint.mono_right (Finset.erase_subset x _) (show Disjoint ((A).fv) ((((syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))).fv).erase y) from (Disjoint.mono_right (Finset.erase_subset y _) (show Disjoint ((A).fv) (((syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]; exact (show Disjoint ((A).fv) ((((syn_csn (.cv x))).fv) ∪ (((syn_csn (.cv y))).fv) ∪ (((syn_cfv (syn_c1st) (.cv u))).fv)) from (Finset.disjoint_union_right.mpr ⟨(Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((syn_csn (.cv x))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((A).fv) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact dv_A_x)))))))), (show Disjoint ((A).fv) (((syn_csn (.cv y))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((A).fv) (((Class.cv y)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (A).fv from (by exact dv_A_y))))))))⟩), (show Disjoint ((A).fv) (((syn_cfv (syn_c1st) (.cv u))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (A).fv from (by exact dv_A_u)))))), (show Disjoint ((A).fv) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))⟩)))))))), (show Disjoint ((A).fv) (((({x} : Finset Var)).erase y).erase x) from (Disjoint.mono_right (Finset.erase_subset x _) (show Disjoint ((A).fv) ((({x} : Finset Var)).erase y) from (Disjoint.mono_right (Finset.erase_subset y _) (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact dv_A_x))))))))⟩))))
  have p0000 :=
    @g_hwcnwendv u (syn_cpw1 A) dv_cache_0001
  have p0001 :=
    @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0002 :=
    @g_pw1ss1c A
  have p0003 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0002
  have p0004 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A) (syn_c1c) p0001 p0003
  have p0005 :=
    @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0006 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0004 p0005
  have p0007 :=
    @g_breq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) p0006
  have p0008 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0000 p0007
  have p0009 :=
    @g_hwcnsupp u (syn_cpw1 A)
  have p0010 :=
    @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0011 :=
    @g_pw1ss1c A
  have p0012 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0011
  have p0013 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A) (syn_c1c) p0010 p0012
  have p0014 :=
    @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0015 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0013 p0014
  have p0016 :=
    @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0017 :=
    @g_pw1ss1c A
  have p0018 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0017
  have p0019 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A) (syn_c1c) p0016 p0018
  have p0020 :=
    @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0021 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0019 p0020
  have p0022 :=
    @g_xpeq12d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0015 p0021
  have p0023 :=
    @g_sseq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u)) p0022
  have p0024 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) p0009 p0023
  have p0025 :=
    @g_sidownrecoverclndv x y (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0026 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (.classEq (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cfv (syn_c1st) (.cv u))) p0024 p0025
  have p0027 :=
    @g_breq1d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cfv (syn_c1st) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0026
  have p0028 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wbr (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cwe) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0008 p0027
  have p0029 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0030 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0029
  have p0031 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0032 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0031
  have p0033 :=
    @g_siwereflectndv (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) p0030 p0032
  have p0034 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wbr (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cwe) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cwe) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0028 p0033
  have p0035 :=
    @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0036 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0037 :=
    @g_pw1subunissclndv A (syn_cfv (syn_c2nd) (.cv u)) p0036
  have p0038 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A)) (syn_wss (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) A) p0035 p0037
  have p0039 :=
    @g_jca (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wbr (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cwe) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) A) p0034 p0038
  have p0040 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0041 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0040
  have p0042 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0043 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0042
  have p0044 :=
    @g_elhwcodes A (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) dv_cache_0007 p0041 p0043
  have p0045 :=
    @g_biimpri (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A)) (syn_wa (syn_wbr (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cwe) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) A)) p0044
  have p0046 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wa (syn_wbr (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cwe) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) A)) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A)) p0039 p0045
  have p0047 :=
    @g_hwcnsupp u (syn_cpw1 A)
  have p0048 :=
    @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0049 :=
    @g_pw1ss1c A
  have p0050 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0049
  have p0051 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A) (syn_c1c) p0048 p0050
  have p0052 :=
    @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0053 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0051 p0052
  have p0054 :=
    @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0055 :=
    @g_pw1ss1c A
  have p0056 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0055
  have p0057 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A) (syn_c1c) p0054 p0056
  have p0058 :=
    @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0059 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0057 p0058
  have p0060 :=
    @g_xpeq12d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0053 p0059
  have p0061 :=
    @g_sseq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u)) p0060
  have p0062 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) p0047 p0061
  have p0063 :=
    @g_sidownsuppclndv x y (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0064 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cxp (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0062 p0063
  have p0065 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0066 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0065
  have p0067 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0068 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0067
  have p0069 :=
    @g_opfv1st (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0066 p0068
  have p0070 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0071 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0070
  have p0072 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0073 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0072
  have p0074 :=
    @g_opfv2nd (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0071 p0073
  have p0075 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0076 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0075
  have p0077 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0078 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0077
  have p0079 :=
    @g_opfv2nd (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0076 p0078
  have p0080 :=
    @g_xpeq12i (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0074 p0079
  have p0081 :=
    @g_sseq12i (syn_cfv (syn_c1st) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0069 p0080
  have p0082 :=
    @g_a1i (syn_wb (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wss (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cxp (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0081
  have p0083 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wss (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cxp (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0064 p0082
  have p0084 :=
    @g_jca (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) p0046 p0083
  have p0085 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0086 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0085
  have p0087 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0088 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0087
  have p0089 :=
    @g_opex (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0086 p0088
  have p0090 :=
    @g_elhwcncl A (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))
  have p0091 :=
    Nominal.mp p0089 p0090
  have p0092 :=
    @g_biimpri (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)) (syn_wa (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))) p0091
  have p0093 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wa (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)) p0084 p0092
  exact p0093

noncomputable def g_hnsireversecodeidndv
    (x : Var) (y : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv u) (syn_cop (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ∉ ((syn_cpw1 A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cuni (syn_cfv (syn_c2nd) (.cv u)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cuni (syn_cfv (syn_c2nd) (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_hwcnpair u (syn_cpw1 A)
  have p0001 :=
    @g_hwcnsupp u (syn_cpw1 A)
  have p0002 :=
    @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0003 :=
    @g_pw1ss1c A
  have p0004 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0003
  have p0005 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A) (syn_c1c) p0002 p0004
  have p0006 :=
    @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0007 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0005 p0006
  have p0008 :=
    @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0009 :=
    @g_pw1ss1c A
  have p0010 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0009
  have p0011 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A) (syn_c1c) p0008 p0010
  have p0012 :=
    @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0013 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0011 p0012
  have p0014 :=
    @g_xpeq12d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0007 p0013
  have p0015 :=
    @g_sseq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (.cv u)) p0014
  have p0016 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) p0001 p0015
  have p0017 :=
    @g_sidownrecoverclndv x y (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0018 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (.classEq (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cfv (syn_c1st) (.cv u))) p0016 p0017
  have p0019 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cfv (syn_c1st) (.cv u)) p0018
  have p0020 :=
    @g_hwcnbase u (syn_cpw1 A) dv_cache_0001
  have p0021 :=
    @g_pw1ss1c A
  have p0022 :=
    @g_a1i (syn_wss (syn_cpw1 A) (syn_c1c)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0021
  have p0023 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 A) (syn_c1c) p0020 p0022
  have p0024 :=
    @g_eqpw1uni (syn_cfv (syn_c2nd) (.cv u))
  have p0025 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_c1c)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0023 p0024
  have p0026 :=
    @g_opeq12d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c1st) (.cv u)) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0019 p0025
  have p0027 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cop (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0000 p0026
  exact p0027

#print axioms g_hnsireversecodeidndv

end NFChoice.DirectNominalPrf.WPPReplay
