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
import NominalWPPReplayChunk014Compact001Part024

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

noncomputable def g_fdcodesub2
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) (hyp_fdcodesub2_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcodesub2_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcodesub2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wss C D)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
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
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
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
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (A).fv from (by exact fresh_y_not_A))))))
  have dv_cache_0003 : Disjoint (A).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0004 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : Disjoint (B).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (B).fv from (by exact fresh_y_not_B))))))
  have dv_cache_0006 : Disjoint (B).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (B).fv from (by exact fresh_x_not_B))))))
  have dv_cache_0007 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : Disjoint ((Class.cv y)).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint ((Class.cv y)).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (y), NFChoice.Compiler.CoreFVSimp.fv_class_cv (x)]; exact (show Disjoint (({y} : Finset Var)) (({x} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))
  have dv_cache_0009 : Disjoint ((Class.cv y)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint ((Class.cv y)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0010 : Disjoint ((Class.cv x)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0011 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0015 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0017 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0019 : y ∉ ((syn_cfdrow R A B (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : Disjoint (A).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0022 : Disjoint (B).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0023 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0024 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0030 : y ∉ ((Wff.classMem (.cv x) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : y ∉ ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcode, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, fresh_y_not_D, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : x ∉ ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcode, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)
  have p0001 :=
    @g_eqid (syn_cfdrow R A B (.cv x))
  have p0002 :=
    @g_a1i (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) p0001
  have p0003 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv x) C) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x))) p0000 p0002
  have p0004 :=
    @g_fdroweq4 A B (.cv y) (.cv x) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0005 :=
    @g_eqeq2d (.classEq (.cv y) (.cv x)) (syn_cfdrow R A B (.cv y)) (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x)) p0004
  have p0006 :=
    @g_rspcev (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x))) y (.cv x) C dv_cache_0011 dv_cache_0012 dv_cache_0013 p0005
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wa (.classMem (.cv x) C) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x)))) (syn_wrex y C (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) p0003 p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)
  have p0009 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0010 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0009 p0010
  have p0012 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A) p0011 p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wbr R (syn_cwe) A) p0008 p0013
  have p0015 :=
    @g_fdrowex2 A B (.cv x) R dv_cache_0001 dv_cache_0003 dv_cache_0004 dv_cache_0006 dv_cache_0007 dv_cache_0010 hyp_fdcodesub2_1 hyp_fdcodesub2_2 hyp_fdcodesub2_3
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrow R A B (.cv x)) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_elfdcode2g y A B C (syn_cfdrow R A B (.cv x)) R dv_cache_0001 dv_cache_0014 dv_cache_0004 dv_cache_0015 dv_cache_0016 dv_cache_0007 dv_cache_0017 dv_cache_0018 dv_cache_0012 dv_cache_0019 dv_cache_0020
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (syn_cfdrow R A B (.cv x)) (syn_cvv)) (syn_wb (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B C)) (syn_wrex y C (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))) p0016 p0017
  have p0019 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B C)) (syn_wrex y C (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) p0007 p0018
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)
  have p0021 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)) p0020 p0021
  have p0023 :=
    @g_eleq2d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_cfdcode R A B C) (syn_cfdcode R A B D) (syn_cfdrow R A B (.cv x)) p0022
  have p0024 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B C)) (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B D)) p0019 p0023
  have p0025 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)
  have p0026 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0027 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0026 p0027
  have p0029 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0030 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A) p0028 p0029
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wbr R (syn_cwe) A) p0025 p0030
  have p0032 :=
    @g_fdrowex2 A B (.cv x) R dv_cache_0001 dv_cache_0003 dv_cache_0004 dv_cache_0006 dv_cache_0007 dv_cache_0010 hyp_fdcodesub2_1 hyp_fdcodesub2_2 hyp_fdcodesub2_3
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrow R A B (.cv x)) (syn_cvv)) p0031 p0032
  have p0034 :=
    @g_elfdcode2g y A B D (syn_cfdrow R A B (.cv x)) R dv_cache_0001 dv_cache_0021 dv_cache_0004 dv_cache_0015 dv_cache_0022 dv_cache_0007 dv_cache_0017 dv_cache_0023 dv_cache_0024 dv_cache_0019 dv_cache_0020
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (syn_cfdrow R A B (.cv x)) (syn_cvv)) (syn_wb (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B D)) (syn_wrex y D (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))) p0033 p0034
  have p0036 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B D)) (syn_wrex y D (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) p0024 p0035
  have p0037 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0038 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)
  have p0039 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0037 p0038
  have p0040 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0041 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) p0040 p0041
  have p0043 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)
  have p0044 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0045 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0044 p0045
  have p0047 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A) p0046 p0047
  have p0049 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wbr R (syn_cwe) A) p0043 p0048
  have p0050 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wbr R (syn_cwe) A) p0042 p0049
  have p0051 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0052 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) p0051 p0052
  have p0054 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)
  have p0055 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)
  have p0056 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0057 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0058 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (.classMem C A) (.classMem D A)) p0056 p0057
  have p0059 :=
    @g_simpl (.classMem C A) (.classMem D A)
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (.classMem C A) (.classMem D A)) (.classMem C A) p0058 p0059
  have p0061 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0062 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0061 p0062
  have p0064 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0065 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wss A (syn_cpw B)) p0063 p0064
  have p0066 :=
    @g_sseld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) A (syn_cpw B) C p0065
  have p0067 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem C A) (.classMem C (syn_cpw B)) p0060 p0066
  have p0068 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0069 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0070 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (.classMem C A) (.classMem D A)) p0068 p0069
  have p0071 :=
    @g_simpl (.classMem C A) (.classMem D A)
  have p0072 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (.classMem C A) (.classMem D A)) (.classMem C A) p0070 p0071
  have p0073 :=
    @g_elex C A
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem C A) (.classMem C (syn_cvv)) p0072 p0073
  have p0075 :=
    @g_elpwg C B (syn_cvv)
  have p0076 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem C (syn_cvv)) (syn_wb (.classMem C (syn_cpw B)) (syn_wss C B)) p0074 p0075
  have p0077 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem C (syn_cpw B)) (syn_wss C B) p0067 p0076
  have p0078 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wss C B) p0055 p0077
  have p0079 :=
    @g_sseld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) C B (.cv x) p0078
  have p0080 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv x) C) (.classMem (.cv x) B) p0054 p0079
  have p0081 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv x) B) p0053 p0080
  have p0082 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0083 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)
  have p0084 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0082 p0083
  have p0085 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0086 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)
  have p0087 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) p0085 p0086
  have p0088 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)
  have p0089 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0090 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (.classMem C A) (.classMem D A)) p0089 p0090
  have p0092 :=
    @g_simpr (.classMem C A) (.classMem D A)
  have p0093 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (.classMem C A) (.classMem D A)) (.classMem D A) p0091 p0092
  have p0094 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0095 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0096 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0094 p0095
  have p0097 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0098 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wss A (syn_cpw B)) p0096 p0097
  have p0099 :=
    @g_sseld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) A (syn_cpw B) D p0098
  have p0100 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem D A) (.classMem D (syn_cpw B)) p0093 p0099
  have p0101 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0102 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0103 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (.classMem C A) (.classMem D A)) p0101 p0102
  have p0104 :=
    @g_simpr (.classMem C A) (.classMem D A)
  have p0105 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (.classMem C A) (.classMem D A)) (.classMem D A) p0103 p0104
  have p0106 :=
    @g_elex D A
  have p0107 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem D A) (.classMem D (syn_cvv)) p0105 p0106
  have p0108 :=
    @g_elpwg D B (syn_cvv)
  have p0109 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem D (syn_cvv)) (syn_wb (.classMem D (syn_cpw B)) (syn_wss D B)) p0107 p0108
  have p0110 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem D (syn_cpw B)) (syn_wss D B) p0100 p0109
  have p0111 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wss D B) p0088 p0110
  have p0112 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wss D B) p0087 p0111
  have p0113 :=
    @g_sseld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) D B (.cv y) p0112
  have p0114 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem (.cv y) D) (.classMem (.cv y) B) p0084 p0113
  have p0115 :=
    @g_n_3jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B) p0050 p0081 p0114
  have p0116 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0117 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0115 p0116
  have p0118 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0119 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)
  have p0120 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) p0118 p0119
  have p0121 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)
  have p0122 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) p0120 p0121
  have p0123 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0124 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0125 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (.classMem C A) (.classMem D A)) p0123 p0124
  have p0126 :=
    @g_simpr (.classMem C A) (.classMem D A)
  have p0127 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (.classMem C A) (.classMem D A)) (.classMem D A) p0125 p0126
  have p0128 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem D A) p0122 p0127
  have p0129 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem D A) p0117 p0128
  have p0130 :=
    @g_fdroweqmem x y A B D R dv_cache_0001 dv_cache_0021 dv_cache_0004 dv_cache_0025 dv_cache_0015 dv_cache_0022 dv_cache_0007 dv_cache_0026 dv_cache_0017 dv_cache_0023 dv_cache_0027 dv_cache_0024 dv_cache_0028 dv_cache_0020 dv_cache_0029
  have p0131 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem D A)) (syn_wb (.classMem (.cv x) D) (.classMem (.cv y) D)) p0129 p0130
  have p0132 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem (.cv x) D) (.classMem (.cv y) D) p0039 p0131
  have p0133 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classMem (.cv y) D)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) (.classMem (.cv x) D) p0132
  have p0134 :=
    @g_rexlimdva (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) (.classMem (.cv x) D) y D dv_cache_0030 dv_cache_0031 p0133
  have p0135 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C)) (syn_wrex y D (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem (.cv x) D) p0036 p0134
  have p0136 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C) (.classMem (.cv x) D) p0135
  have p0137 :=
    @g_ssrdv (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) x C D dv_cache_0032 dv_cache_0027 dv_cache_0033 p0136
  exact p0137

#print axioms g_fdcodesub2

end NFChoice.DirectNominalPrf.WPPReplay
