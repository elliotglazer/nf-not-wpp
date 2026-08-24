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
import NominalWPPReplayChunk014Compact001Part019

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

noncomputable def g_fdrowsep
    (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (d : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_R_d : d ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_d_x : d ≠ x) (dv_d_y : d ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ ({d} : Finset Var)
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have dv_cache_0017 : Disjoint (A).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show Disjoint (A).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (A).fv from (by exact dv_A_d))))))
  have dv_cache_0018 : Disjoint (B).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show Disjoint (B).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (B).fv from (by exact dv_B_x))))))
  have dv_cache_0019 : Disjoint (B).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show Disjoint (B).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (B).fv from (by exact dv_B_d))))))
  have dv_cache_0020 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0021 : Disjoint ((Class.cv x)).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show Disjoint ((Class.cv x)).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x), NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)]; exact (show Disjoint (({x} : Finset Var)) (({d} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ d from (by exact Ne.symm dv_d_x))))))))
  have dv_cache_0022 : Disjoint ((Class.cv d)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show Disjoint ((Class.cv d)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({d} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show d ∉ (R).fv from (by exact dv_R_d))))))
  have dv_cache_0023 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : d ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show d ≠ x from (by exact dv_d_x))
  have dv_cache_0031 : d ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show d ≠ y from (by exact dv_d_y))
  have dv_cache_0032 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0033 : Disjoint (B).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show Disjoint (B).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (B).fv from (by exact dv_B_y))))))
  have dv_cache_0034 : Disjoint ((Class.cv y)).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show Disjoint ((Class.cv y)).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (y), NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)]; exact (show Disjoint (({y} : Finset Var)) (({d} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show y ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ d from (by exact Ne.symm dv_d_y))))))))
  have p0000 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
  have p0001 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0002 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) p0001
  have p0003 :=
    @g_simplr (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))
  have p0004 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) p0002 p0003
  have p0005 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) p0000 p0004
  have p0006 :=
    @g_sep2valJp (.cv x) (.cv y) d dv_cache_0006 dv_cache_0009 dv_cache_0012
  have p0007 :=
    @g_xor (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d))
  have p0008 :=
    @g_bicomi (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d)))) (syn_wo (syn_wa (.classMem (.cv x) (.cv d)) (.neg (.classMem (.cv y) (.cv d)))) (syn_wa (.classMem (.cv y) (.cv d)) (.neg (.classMem (.cv x) (.cv d))))) p0007
  have p0009 :=
    @g_bitri (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wo (syn_wa (.classMem (.cv x) (.cv d)) (.neg (.classMem (.cv y) (.cv d)))) (syn_wa (.classMem (.cv y) (.cv d)) (.neg (.classMem (.cv x) (.cv d))))) (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d)))) p0006 p0008
  have p0010 :=
    @g_biimpi (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d)))) p0009
  have p0011 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d)))) p0005 p0010
  have p0012 :=
    @g_elfdrowg A B (.cv x) (.cv d) R dv_cache_0016 dv_cache_0001 dv_cache_0017 dv_cache_0003 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0007 dv_cache_0022
  have p0013 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x))) (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv x) (.cv d)))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) p0012
  have p0014 :=
    @g_fpivelfdif x y A B R d dv_cache_0016 dv_cache_0003 dv_cache_0005 dv_cache_0023 dv_cache_0024 dv_cache_0020 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0014 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
  have p0015 :=
    @g_biantrurd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv x) (.cv d)) p0014
  have p0016 :=
    @g_bicomd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv x) (.cv d)) (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv x) (.cv d))) p0015
  have p0017 :=
    @g_bitrd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv d) (syn_cfdrow R A B (.cv x))) (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv x) (.cv d))) (.classMem (.cv x) (.cv d)) p0013 p0016
  have p0018 :=
    @g_elfdrowg A B (.cv y) (.cv d) R dv_cache_0016 dv_cache_0002 dv_cache_0017 dv_cache_0003 dv_cache_0033 dv_cache_0019 dv_cache_0020 dv_cache_0034 dv_cache_0010 dv_cache_0022
  have p0019 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv y))) (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv y) (.cv d)))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) p0018
  have p0020 :=
    @g_fpivelfdif x y A B R d dv_cache_0016 dv_cache_0003 dv_cache_0005 dv_cache_0023 dv_cache_0024 dv_cache_0020 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0014 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
  have p0021 :=
    @g_biantrurd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv y) (.cv d)) p0020
  have p0022 :=
    @g_bicomd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv y) (.cv d)) (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv y) (.cv d))) p0021
  have p0023 :=
    @g_bitrd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv d) (syn_cfdrow R A B (.cv y))) (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem (.cv y) (.cv d))) (.classMem (.cv y) (.cv d)) p0019 p0022
  have p0024 :=
    @g_bibi12d (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.classMem (.cv d) (syn_cfdrow R A B (.cv x))) (.classMem (.cv x) (.cv d)) (.classMem (.cv d) (syn_cfdrow R A B (.cv y))) (.classMem (.cv y) (.cv d)) p0017 p0023
  have p0025 :=
    @g_notbid (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x))) (.classMem (.cv d) (syn_cfdrow R A B (.cv y)))) (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d))) p0024
  have p0026 :=
    @g_mpbird (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.neg (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x))) (.classMem (.cv d) (syn_cfdrow R A B (.cv y))))) (.neg (syn_wb (.classMem (.cv x) (.cv d)) (.classMem (.cv y) (.cv d)))) p0011 p0025
  have p0027 :=
    @g_eleq2 (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)) (.cv d)
  have p0028 :=
    @g_necon3bi (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x))) (.classMem (.cv d) (syn_cfdrow R A B (.cv y)))) (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)) p0027
  have p0029 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (.neg (syn_wb (.classMem (.cv d) (syn_cfdrow R A B (.cv x))) (.classMem (.cv d) (syn_cfdrow R A B (.cv y))))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0026 p0028
  exact p0029

noncomputable def g_sep2ex2
    (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classMem (syn_csep2 (.cv x) (.cv y)) (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var)
  let c : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have fresh_c_ne_y : c ≠ y := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_c : y ≠ c :=
    Ne.symm fresh_c_ne_y
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_c_ne_b : c ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_c : b ≠ c :=
    Ne.symm fresh_c_ne_b
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv := by
    exact (show Disjoint ((Class.cv x)).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x), NFChoice.Compiler.CoreFVSimp.fv_class_cv (y)]; exact (show Disjoint (({x} : Finset Var)) (({y} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y))))))))
  have dv_cache_0002 : b ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : c ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : c ∉ ((Wff.classMem (.cv x) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : c ∉ ((Wff.classMem (.cv y) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((syn_csep2 (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_c, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : c ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : c ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_sep2valJp (.cv x) (.cv y) b dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_elsymdif (.cv b) (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c)))
  have p0002 :=
    @g_vex b
  have p0003 :=
    @g_eleq2 (.cv c) (.cv b) (.cv x)
  have p0004 :=
    @g_elab (.classMem (.cv x) (.cv c)) (.classMem (.cv x) (.cv b)) c (.cv b) dv_cache_0004 dv_cache_0005 p0002 p0003
  have p0005 :=
    @g_vex b
  have p0006 :=
    @g_eleq2 (.cv c) (.cv b) (.cv y)
  have p0007 :=
    @g_elab (.classMem (.cv y) (.cv c)) (.classMem (.cv y) (.cv b)) c (.cv b) dv_cache_0004 dv_cache_0006 p0005 p0006
  have p0008 :=
    @g_bibi12i (.classMem (.cv b) (.cab c (.classMem (.cv x) (.cv c)))) (.classMem (.cv x) (.cv b)) (.classMem (.cv b) (.cab c (.classMem (.cv y) (.cv c)))) (.classMem (.cv y) (.cv b)) p0004 p0007
  have p0009 :=
    @g_notbii (syn_wb (.classMem (.cv b) (.cab c (.classMem (.cv x) (.cv c)))) (.classMem (.cv b) (.cab c (.classMem (.cv y) (.cv c))))) (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))) p0008
  have p0010 :=
    @g_bitri (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))))) (.neg (syn_wb (.classMem (.cv b) (.cab c (.classMem (.cv x) (.cv c)))) (.classMem (.cv b) (.cab c (.classMem (.cv y) (.cv c)))))) (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b)))) p0001 p0009
  have p0011 :=
    @g_xor (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))
  have p0012 :=
    @g_bitri (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))))) (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b)))) (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b)))) (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b))))) p0010 p0011
  have p0013 :=
    @g_bicomi (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))))) (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b)))) (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b))))) p0012
  have p0014 :=
    @g_bitri (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))) (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b)))) (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b))))) (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))))) p0000 p0013
  have p0015 :=
    @g_eqabi (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))))) b (syn_csep2 (.cv x) (.cv y)) dv_cache_0007 p0014
  have p0016 :=
    @g_abid2 b (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c)))) dv_cache_0008
  have p0017 :=
    @g_eqtri (syn_csep2 (.cv x) (.cv y)) (.cab b (.classMem (.cv b) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c)))))) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c)))) p0015 p0016
  have p0018 :=
    @g_setswithex c (.cv x) dv_cache_0009
  have p0019 :=
    @g_setswithex c (.cv y) dv_cache_0010
  have p0020 :=
    @g_symdifex (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c))) p0018 p0019
  have p0021 :=
    @g_eqeltri (syn_csep2 (.cv x) (.cv y)) (syn_csymdif (.cab c (.classMem (.cv x) (.cv c))) (.cab c (.classMem (.cv y) (.cv c)))) (syn_cvv) p0017 p0020
  exact p0021

#print axioms g_sep2ex2

end NFChoice.DirectNominalPrf.WPPReplay
