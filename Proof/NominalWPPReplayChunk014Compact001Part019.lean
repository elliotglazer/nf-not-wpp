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
import NominalWPPReplayChunk014Compact001Part018

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

noncomputable def g_fpivelfdif
    (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_R_d : d ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_d_x : d ≠ x) (dv_d_y : d ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv d) (syn_cfdif R A B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ ({d} : Finset Var)
  let b : Var := freshVar proofSupport 0
  let c : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_d : b ≠ d := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_b : d ≠ b :=
    Ne.symm fresh_b_ne_d
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have fresh_c_ne_y : c ≠ y := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_c : y ≠ c :=
    Ne.symm fresh_c_ne_y
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_ne_d : c ≠ d := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_c : d ≠ c :=
    Ne.symm fresh_c_ne_d
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_p : y ≠ p :=
    Ne.symm fresh_p_ne_y
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_d : p ≠ d := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_p : d ≠ p :=
    Ne.symm fresh_p_ne_d
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have fresh_b_ne_p : b ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_b : p ≠ b :=
    Ne.symm fresh_b_ne_p
  have fresh_c_ne_p : c ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_c : p ≠ c :=
    Ne.symm fresh_c_ne_p
  have dv_cache_0001 : Disjoint (A).fv ((Class.cv x)).fv := by
    exact (show Disjoint (A).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact dv_A_x))))))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (A).fv from (by exact dv_A_y))))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : c ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint ((Class.cv x)).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x), NFChoice.Compiler.CoreFVSimp.fv_class_cv (y)]; exact (show Disjoint (({x} : Finset Var)) (({y} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y))))))))
  have dv_cache_0007 : Disjoint ((Class.cv x)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact dv_R_x))))))
  have dv_cache_0008 : c ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : Disjoint ((Class.cv y)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint ((Class.cv y)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show y ∉ (R).fv from (by exact dv_R_y))))))
  have dv_cache_0011 : c ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : d ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : c ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : c ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0016 : Disjoint (A).fv (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0017 : Disjoint (A).fv ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show Disjoint (A).fv ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({c} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show c ∉ (A).fv from (by exact fresh_c_not_A))))))
  have dv_cache_0018 : Disjoint (B).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show Disjoint (B).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (B).fv from (by exact dv_B_x))))))
  have dv_cache_0019 : Disjoint (B).fv ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show Disjoint (B).fv ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({c} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show c ∉ (B).fv from (by exact fresh_c_not_B))))))
  have dv_cache_0020 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0021 : Disjoint ((Class.cv x)).fv ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show Disjoint ((Class.cv x)).fv ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x), NFChoice.Compiler.CoreFVSimp.fv_class_cv (c)]; exact (show Disjoint (({x} : Finset Var)) (({c} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ c from (by exact fresh_x_ne_c))))))))
  have dv_cache_0022 : Disjoint ((Class.cv c)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show Disjoint ((Class.cv c)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({c} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show c ∉ (R).fv from (by exact fresh_c_not_R))))))
  have dv_cache_0023 : Disjoint (A).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show Disjoint (A).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0024 : Disjoint (A).fv ((syn_copk (.cv x) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show Disjoint (A).fv ((syn_copk (.cv x) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((A).fv) ((((Class.cv x)).fv) ∪ (((Class.cv c)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact dv_A_x)))))), (show Disjoint ((A).fv) (((Class.cv c)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({c} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show c ∉ (A).fv from (by exact fresh_c_not_A))))))⟩))))
  have dv_cache_0025 : Disjoint (B).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show Disjoint (B).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0026 : Disjoint (B).fv ((syn_copk (.cv x) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (show Disjoint (B).fv ((syn_copk (.cv x) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((B).fv) ((((Class.cv x)).fv) ∪ (((Class.cv c)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((B).fv) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (B).fv from (by exact dv_B_x)))))), (show Disjoint ((B).fv) (((Class.cv c)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({c} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show c ∉ (B).fv from (by exact fresh_c_not_B))))))⟩))))
  have dv_cache_0027 : Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint (({p} : Finset Var)) ((((Class.cv x)).fv) ∪ (((Class.cv c)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({p} : Finset Var)) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) (({x} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show p ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ x from (by exact fresh_p_ne_x)))))))), (show Disjoint (({p} : Finset Var)) (((Class.cv c)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) (({c} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show p ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ c from (by exact fresh_p_ne_c))))))))⟩))))
  have dv_cache_0028 : Disjoint ((Class.cv p)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show Disjoint ((Class.cv p)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0029 : Disjoint ((syn_copk (.cv x) (.cv c))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show Disjoint ((syn_copk (.cv x) (.cv c))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((((Class.cv x)).fv) ∪ (((Class.cv c)).fv)) ((R).fv) from (Finset.disjoint_union_left.mpr ⟨(show Disjoint (((Class.cv x)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact dv_R_x)))))), (show Disjoint (((Class.cv c)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({c} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show c ∉ (R).fv from (by exact fresh_c_not_R))))))⟩))))
  have dv_cache_0030 : Disjoint (A).fv ((syn_copk (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show Disjoint (A).fv ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((A).fv) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact dv_A_x)))))), (show Disjoint ((A).fv) (((Class.cv y)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (A).fv from (by exact dv_A_y))))))⟩))))
  have dv_cache_0031 : Disjoint (B).fv ((syn_copk (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show Disjoint (B).fv ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((B).fv) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((B).fv) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (B).fv from (by exact dv_B_x)))))), (show Disjoint ((B).fv) (((Class.cv y)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (B).fv from (by exact dv_B_y))))))⟩))))
  have dv_cache_0032 : Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint (({p} : Finset Var)) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({p} : Finset Var)) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) (({x} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show p ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ x from (by exact fresh_p_ne_x)))))))), (show Disjoint (({p} : Finset Var)) (((Class.cv y)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) (({y} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show p ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ y from (by exact fresh_p_ne_y))))))))⟩))))
  have dv_cache_0033 : Disjoint ((syn_copk (.cv x) (.cv y))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show Disjoint ((syn_copk (.cv x) (.cv y))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) ((R).fv) from (Finset.disjoint_union_left.mpr ⟨(show Disjoint (((Class.cv x)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact dv_R_x)))))), (show Disjoint (((Class.cv y)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show y ∉ (R).fv from (by exact dv_R_y))))))⟩))))
  have dv_cache_0034 : p ∉ ((syn_copk (.cv x) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : p ∉ ((Wff.imp (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_not_B, fresh_p_not_R, fresh_p_not_A, fresh_p_ne_x, fresh_p_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : Disjoint (B).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show Disjoint (B).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (B).fv from (by exact dv_B_y))))))
  have dv_cache_0037 : c ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : c ∉ ((Wff.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_d, fresh_c_not_A, fresh_c_ne_x, fresh_c_ne_y, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : c ∉ ((syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, fresh_c_not_B, fresh_c_not_R, fresh_c_not_A, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : Disjoint (A).fv ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (show Disjoint (A).fv ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({b} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show b ∉ (A).fv from (by exact fresh_b_not_A))))))
  have dv_cache_0041 : Disjoint (B).fv ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (show Disjoint (B).fv ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({b} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show b ∉ (B).fv from (by exact fresh_b_not_B))))))
  have dv_cache_0042 : Disjoint ((Class.cv b)).fv ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (show Disjoint ((Class.cv b)).fv ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (b), NFChoice.Compiler.CoreFVSimp.fv_class_cv (c)]; exact (show Disjoint (({b} : Finset Var)) (({c} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c))))))))
  have dv_cache_0043 : Disjoint ((Class.cv b)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (show Disjoint ((Class.cv b)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({b} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show b ∉ (R).fv from (by exact fresh_b_not_R))))))
  have dv_cache_0044 : Disjoint (A).fv ((syn_copk (.cv b) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (show Disjoint (A).fv ((syn_copk (.cv b) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((A).fv) ((((Class.cv b)).fv) ∪ (((Class.cv c)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv b)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({b} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show b ∉ (A).fv from (by exact fresh_b_not_A)))))), (show Disjoint ((A).fv) (((Class.cv c)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({c} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show c ∉ (A).fv from (by exact fresh_c_not_A))))))⟩))))
  have dv_cache_0045 : Disjoint (B).fv ((syn_copk (.cv b) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact (show Disjoint (B).fv ((syn_copk (.cv b) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((B).fv) ((((Class.cv b)).fv) ∪ (((Class.cv c)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((B).fv) (((Class.cv b)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({b} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show b ∉ (B).fv from (by exact fresh_b_not_B)))))), (show Disjoint ((B).fv) (((Class.cv c)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({c} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show c ∉ (B).fv from (by exact fresh_c_not_B))))))⟩))))
  have dv_cache_0046 : Disjoint ((Class.cv p)).fv ((syn_copk (.cv b) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (show Disjoint ((Class.cv p)).fv ((syn_copk (.cv b) (.cv c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint (({p} : Finset Var)) ((((Class.cv b)).fv) ∪ (((Class.cv c)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({p} : Finset Var)) (((Class.cv b)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) (({b} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show p ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ b from (by exact fresh_p_ne_b)))))))), (show Disjoint (({p} : Finset Var)) (((Class.cv c)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) (({c} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show p ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ c from (by exact fresh_p_ne_c))))))))⟩))))
  have dv_cache_0047 : Disjoint ((syn_copk (.cv b) (.cv c))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (show Disjoint ((syn_copk (.cv b) (.cv c))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((((Class.cv b)).fv) ∪ (((Class.cv c)).fv)) ((R).fv) from (Finset.disjoint_union_left.mpr ⟨(show Disjoint (((Class.cv b)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({b} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show b ∉ (R).fv from (by exact fresh_b_not_R)))))), (show Disjoint (((Class.cv c)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({c} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show c ∉ (R).fv from (by exact fresh_c_not_R))))))⟩))))
  have dv_cache_0048 : p ∉ ((syn_copk (.cv b) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_b, fresh_p_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0049 : p ∉ ((Wff.imp (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_not_B, fresh_p_not_R, fresh_p_not_A, fresh_p_ne_x, fresh_p_ne_b, fresh_p_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0050 : c ∉ ((syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, fresh_c_not_B, fresh_c_not_R, fresh_c_not_A, fresh_c_ne_x, fresh_c_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0051 : b ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0052 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0053 : b ∉ ((syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, fresh_b_ne_d, fresh_b_not_A, fresh_b_ne_x, fresh_b_ne_c, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0054 : b ∉ ((syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, fresh_b_not_B, fresh_b_not_R, fresh_b_not_A, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0055 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0056 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0057 : b ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0058 : d ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact (show d ≠ b from (by exact fresh_d_ne_b))
  have dv_cache_0059 : d ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0060 : b ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have p0000 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) p0000
  have p0002 :=
    @g_simpll (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))
  have p0003 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (.classMem (.cv d) A) p0001 p0002
  have p0004 :=
    @g_a1i (.imp (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A)) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) p0003
  have p0005 :=
    @g_simp3 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0006 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))
  have p0007 :=
    @g_simp1 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0008 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr R (syn_cwe) A) p0006 p0007
  have p0009 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))
  have p0010 :=
    @g_simp2 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0011 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv x) B) p0009 p0010
  have p0012 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))
  have p0013 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))
  have p0014 :=
    @g_simp3 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0015 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv y) B) p0013 p0014
  have p0016 :=
    @g_eqeltrd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (.cv c) (.cv y) B p0012 p0015
  have p0017 :=
    @g_jca (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (.classMem (.cv x) B) (.classMem (.cv c) B) p0011 p0016
  have p0018 :=
    @g_jca (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv c) B)) p0008 p0017
  have p0019 :=
    @g_fdminvalpfpivred A B (.cv x) (.cv c) R dv_cache_0016 dv_cache_0001 dv_cache_0017 dv_cache_0003 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0007 dv_cache_0022
  have p0020 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv c) B))) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfpiv R A (.cv x) (.cv c))) p0018 p0019
  have p0021 :=
    @g_eqcomd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfpiv R A (.cv x) (.cv c)) p0020
  have p0022 :=
    @g_opkex (.cv x) (.cv c)
  have p0023 :=
    @g_simpl (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y)))
  have p0024 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv x) (.cv c)) R dv_cache_0016 dv_cache_0023 dv_cache_0024 dv_cache_0003 dv_cache_0025 dv_cache_0026 dv_cache_0020 dv_cache_0027 dv_cache_0028 dv_cache_0029
  have p0025 :=
    @g_syl (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y)))) (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (.classEq (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))) p0023 p0024
  have p0026 :=
    @g_eqcomd (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y)))) (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) p0025
  have p0027 :=
    @g_simpl (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y)))
  have p0028 :=
    @g_simpr (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y)))
  have p0029 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))
  have p0030 :=
    @g_opkeq2d (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (.cv c) (.cv y) (.cv x) p0029
  have p0031 :=
    @g_syl (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y)))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (.classEq (syn_copk (.cv x) (.cv c)) (syn_copk (.cv x) (.cv y))) p0028 p0030
  have p0032 :=
    @g_eqtrd (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y)))) (.cv p) (syn_copk (.cv x) (.cv c)) (syn_copk (.cv x) (.cv y)) p0027 p0031
  have p0033 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv x) (.cv y)) R dv_cache_0016 dv_cache_0023 dv_cache_0030 dv_cache_0003 dv_cache_0025 dv_cache_0031 dv_cache_0020 dv_cache_0032 dv_cache_0028 dv_cache_0033
  have p0034 :=
    @g_syl (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y)))) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))) (.classEq (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))) p0032 p0033
  have p0035 :=
    @g_eqtrd (syn_wa (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y)))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) p0026 p0034
  have p0036 :=
    @g_ex (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))) p0035
  have p0037 :=
    @g_vtocleg (.imp (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))))) p (syn_copk (.cv x) (.cv c)) (syn_cvv) dv_cache_0034 dv_cache_0035 p0036
  have p0038 :=
    Nominal.mp p0022 p0037
  have p0039 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))
  have p0040 :=
    @g_simp1 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0041 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr R (syn_cwe) A) p0039 p0040
  have p0042 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))
  have p0043 :=
    @g_simp2 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0044 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv x) B) p0042 p0043
  have p0045 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))
  have p0046 :=
    @g_simp3 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0047 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv y) B) p0045 p0046
  have p0048 :=
    @g_jca (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (.classMem (.cv x) B) (.classMem (.cv y) B) p0044 p0047
  have p0049 :=
    @g_jca (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0041 p0048
  have p0050 :=
    @g_fdminvalpfpivred A B (.cv x) (.cv y) R dv_cache_0016 dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0018 dv_cache_0036 dv_cache_0020 dv_cache_0006 dv_cache_0007 dv_cache_0010
  have p0051 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) (syn_cfpiv R A (.cv x) (.cv y))) p0049 p0050
  have p0052 :=
    @g_n_3eqtrd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_cfpiv R A (.cv x) (.cv c)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) (syn_cfpiv R A (.cv x) (.cv y)) p0021 p0038 p0051
  have p0053 :=
    @g_eleq2d (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv c) (.cv y))) (syn_cfpiv R A (.cv x) (.cv c)) (syn_cfpiv R A (.cv x) (.cv y)) (.cv d) p0052
  have p0054 :=
    @g_rspcedv (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) c (.cv y) B dv_cache_0011 dv_cache_0037 dv_cache_0038 dv_cache_0039 p0005 p0053
  have p0055 :=
    @g_simp2 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0056 :=
    @g_simpl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)
  have p0057 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))
  have p0058 :=
    @g_simp1 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0059 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr R (syn_cwe) A) p0057 p0058
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (syn_wbr R (syn_cwe) A) p0056 p0059
  have p0061 :=
    @g_simpl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)
  have p0062 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classEq (.cv b) (.cv x)) p0061 p0062
  have p0064 :=
    @g_simpl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)
  have p0065 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))
  have p0066 :=
    @g_simp2 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0067 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv x) B) p0065 p0066
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv x) B) p0064 p0067
  have p0069 :=
    @g_eqeltrd (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (.cv b) (.cv x) B p0063 p0068
  have p0070 :=
    @g_simpr (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)
  have p0071 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (.classMem (.cv b) B) (.classMem (.cv c) B) p0069 p0070
  have p0072 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv b) B) (.classMem (.cv c) B)) p0060 p0071
  have p0073 :=
    @g_fdminvalpfpivred A B (.cv b) (.cv c) R dv_cache_0016 dv_cache_0040 dv_cache_0017 dv_cache_0003 dv_cache_0041 dv_cache_0019 dv_cache_0020 dv_cache_0042 dv_cache_0043 dv_cache_0022
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv b) B) (.classMem (.cv c) B))) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) (syn_cfpiv R A (.cv b) (.cv c))) p0072 p0073
  have p0075 :=
    @g_eqcomd (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) (syn_cfpiv R A (.cv b) (.cv c)) p0074
  have p0076 :=
    @g_opkex (.cv b) (.cv c)
  have p0077 :=
    @g_simpl (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
  have p0078 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv b) (.cv c)) R dv_cache_0016 dv_cache_0023 dv_cache_0044 dv_cache_0003 dv_cache_0025 dv_cache_0045 dv_cache_0020 dv_cache_0046 dv_cache_0028 dv_cache_0047
  have p0079 :=
    @g_syl (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))) (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (.classEq (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c)))) p0077 p0078
  have p0080 :=
    @g_eqcomd (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))) (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) p0079
  have p0081 :=
    @g_simpl (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
  have p0082 :=
    @g_simpr (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))
  have p0083 :=
    @g_simpl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)
  have p0084 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))
  have p0085 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classEq (.cv b) (.cv x)) p0083 p0084
  have p0086 :=
    @g_opkeq1d (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (.cv b) (.cv x) (.cv c) p0085
  have p0087 :=
    @g_syl (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (.classEq (syn_copk (.cv b) (.cv c)) (syn_copk (.cv x) (.cv c))) p0082 p0086
  have p0088 :=
    @g_eqtrd (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))) (.cv p) (syn_copk (.cv b) (.cv c)) (syn_copk (.cv x) (.cv c)) p0081 p0087
  have p0089 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv x) (.cv c)) R dv_cache_0016 dv_cache_0023 dv_cache_0024 dv_cache_0003 dv_cache_0025 dv_cache_0026 dv_cache_0020 dv_cache_0027 dv_cache_0028 dv_cache_0029
  have p0090 :=
    @g_syl (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))) (.classEq (.cv p) (syn_copk (.cv x) (.cv c))) (.classEq (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))) p0088 p0089
  have p0091 :=
    @g_eqtrd (syn_wa (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B))) (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) p0080 p0090
  have p0092 :=
    @g_ex (.classEq (.cv p) (syn_copk (.cv b) (.cv c))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c)))) p0091
  have p0093 :=
    @g_vtocleg (.imp (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))))) p (syn_copk (.cv b) (.cv c)) (syn_cvv) dv_cache_0048 dv_cache_0049 p0092
  have p0094 :=
    Nominal.mp p0076 p0093
  have p0095 :=
    @g_simpl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)
  have p0096 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))
  have p0097 :=
    @g_simp1 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0098 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr R (syn_cwe) A) p0096 p0097
  have p0099 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (syn_wbr R (syn_cwe) A) p0095 p0098
  have p0100 :=
    @g_simpl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)
  have p0101 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))
  have p0102 :=
    @g_simp2 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0103 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv x) B) p0101 p0102
  have p0104 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv x) B) p0100 p0103
  have p0105 :=
    @g_simpr (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)
  have p0106 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (.classMem (.cv x) B) (.classMem (.cv c) B) p0104 p0105
  have p0107 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv c) B)) p0099 p0106
  have p0108 :=
    @g_fdminvalpfpivred A B (.cv x) (.cv c) R dv_cache_0016 dv_cache_0001 dv_cache_0017 dv_cache_0003 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0007 dv_cache_0022
  have p0109 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv c) B))) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfpiv R A (.cv x) (.cv c))) p0107 p0108
  have p0110 :=
    @g_n_3eqtrd (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_cfpiv R A (.cv b) (.cv c)) (syn_cfdminvalp R A B (syn_copk (.cv b) (.cv c))) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv c))) (syn_cfpiv R A (.cv x) (.cv c)) p0075 p0094 p0109
  have p0111 :=
    @g_eleq2d (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv c) B)) (syn_cfpiv R A (.cv b) (.cv c)) (syn_cfpiv R A (.cv x) (.cv c)) (.cv d) p0110
  have p0112 :=
    @g_rexbidva (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (.cv b) (.cv x))) (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c))) c B dv_cache_0050 p0111
  have p0113 :=
    @g_rspcedv (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c)))) (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c)))) b (.cv x) B dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 p0055 p0112
  have p0114 :=
    @g_syld (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv c)))) (syn_wrex b B (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c))))) p0054 p0113
  have p0115 :=
    @g_jcad (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A) (syn_wrex b B (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c))))) p0004 p0114
  have p0116 :=
    @g_elfdif b c A B R d dv_cache_0016 dv_cache_0003 dv_cache_0005 dv_cache_0055 dv_cache_0004 dv_cache_0020 dv_cache_0056 dv_cache_0052 dv_cache_0037 dv_cache_0014 dv_cache_0057 dv_cache_0013 dv_cache_0058 dv_cache_0059 dv_cache_0060
  have p0117 :=
    @g_biimpri (.classMem (.cv d) (syn_cfdif R A B)) (syn_wa (.classMem (.cv d) A) (syn_wrex b B (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c)))))) p0116
  have p0118 :=
    @g_syl6 (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wa (.classMem (.cv d) A) (syn_wrex b B (syn_wrex c B (.classMem (.cv d) (syn_cfpiv R A (.cv b) (.cv c)))))) (.classMem (.cv d) (syn_cfdif R A B)) p0115 p0117
  have p0119 :=
    @g_imp (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) (syn_cfdif R A B)) p0118
  exact p0119

#print axioms g_fpivelfdif

end NFChoice.DirectNominalPrf.WPPReplay
