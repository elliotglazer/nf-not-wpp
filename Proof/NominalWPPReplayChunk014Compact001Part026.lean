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
import NominalWPPReplayChunk014Compact001Part025

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

noncomputable def g_fdcodeinj2
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) (hyp_fdcodeinj2_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcodeinj2_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcodeinj2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classEq C D)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0007 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : Disjoint (C).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0009 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0010 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0011 : Disjoint (D).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint (D).fv (C).fv from (show Disjoint (D).fv (C).fv from (by exact dv_C_D.symm)))
  have p0000 :=
    @g_fdcodesub2 A B C D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 hyp_fdcodeinj2_1 hyp_fdcodeinj2_2 hyp_fdcodeinj2_3
  have p0001 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0002 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0003 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0001 p0002
  have p0004 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0005 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (.classMem C A) (.classMem D A)) p0004 p0005
  have p0007 :=
    @g_simpr (.classMem C A) (.classMem D A)
  have p0008 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (.classMem C A) (.classMem D A)) (.classMem D A) p0006 p0007
  have p0009 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0010 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (syn_wa (.classMem C A) (.classMem D A)) p0009 p0010
  have p0012 :=
    @g_simpl (.classMem C A) (.classMem D A)
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (.classMem C A) (.classMem D A)) (.classMem C A) p0011 p0012
  have p0014 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem D A) (.classMem C A) p0008 p0013
  have p0015 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem D A) (.classMem C A)) p0003 p0014
  have p0016 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0017 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_cfdcode R A B C) (syn_cfdcode R A B D) p0016
  have p0018 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem D A) (.classMem C A))) (.classEq (syn_cfdcode R A B D) (syn_cfdcode R A B C)) p0015 p0017
  have p0019 :=
    @g_fdcodesub2 A B D C R dv_cache_0001 dv_cache_0003 dv_cache_0002 dv_cache_0004 dv_cache_0006 dv_cache_0005 dv_cache_0007 dv_cache_0011 dv_cache_0010 dv_cache_0009 hyp_fdcodeinj2_1 hyp_fdcodeinj2_2 hyp_fdcodeinj2_3
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem D A) (.classMem C A))) (.classEq (syn_cfdcode R A B D) (syn_cfdcode R A B C))) (syn_wss D C) p0018 p0019
  have p0021 :=
    @g_eqssd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) C D p0000 p0020
  exact p0021

noncomputable def g_wppimagefn
    (R : Class) (hyp_wppimagefn_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cimage R) (syn_cvv)) := by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((syn_cima R (.cv x))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0004 : x ∉ ((syn_cimage R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cimage R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_imaex R (.cv x) hyp_wppimagefn_1 p0000
  have p0002 :=
    @g_eueq y (syn_cima R (.cv x)) dv_cache_0001
  have p0003 :=
    @g_mpbi (.classMem (syn_cima R (.cv x)) (syn_cvv)) (syn_weu y (.classEq (.cv y) (syn_cima R (.cv x)))) p0001 p0002
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_brimage (.cv x) (.cv y) R p0004 p0005
  have p0007 :=
    @g_eubii (syn_wbr (.cv x) (syn_cimage R) (.cv y)) (.classEq (.cv y) (syn_cima R (.cv x))) y p0006
  have p0008 :=
    @g_mpbir (syn_weu y (syn_wbr (.cv x) (syn_cimage R) (.cv y))) (syn_weu y (.classEq (.cv y) (syn_cima R (.cv x)))) p0003 p0007
  have p0009 :=
    @g_rgenw (syn_weu y (syn_wbr (.cv x) (syn_cimage R) (.cv y))) x (syn_cvv) p0008
  have p0010 :=
    @g_fnres x y (syn_cvv) (syn_cimage R) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0011 :=
    @g_mpbir (syn_wfn (syn_cres (syn_cimage R) (syn_cvv)) (syn_cvv)) (syn_wral x (syn_cvv) (syn_weu y (syn_wbr (.cv x) (syn_cimage R) (.cv y)))) p0009 p0010
  have p0012 :=
    @g_resid (syn_cimage R)
  have p0013 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cimage R) (syn_cvv)) (syn_cimage R) p0012
  have p0014 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cimage R) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cimage R) (syn_cvv)) p0011 p0013
  exact p0014

noncomputable def g_wppfvimage
    (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_wppfvimage_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_wppfvimage_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage R) A) (syn_cima R A)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    @g_eqid (syn_cima R A)
  have p0001 :=
    @g_imaex R A hyp_wppfvimage_1 hyp_wppfvimage_2
  have p0002 :=
    @g_brimage A (syn_cima R A) R hyp_wppfvimage_2 p0001
  have p0003 :=
    @g_mpbir (syn_wbr A (syn_cimage R) (syn_cima R A)) (.classEq (syn_cima R A) (syn_cima R A)) p0000 p0002
  have p0004 :=
    @g_tru
  have p0005 :=
    @g_wppimagefn R hyp_wppfvimage_1
  have p0006 :=
    @g_a1i (syn_wfn (syn_cimage R) (syn_cvv)) syn_wtru p0005
  have p0007 :=
    @g_a1i (.classMem A (syn_cvv)) syn_wtru hyp_wppfvimage_2
  have p0008 :=
    @g_jca syn_wtru (syn_wfn (syn_cimage R) (syn_cvv)) (.classMem A (syn_cvv)) p0006 p0007
  have p0009 :=
    Nominal.mp p0004 p0008
  have p0010 :=
    @g_fnbrfvb (syn_cvv) A (syn_cima R A) (syn_cimage R)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_mpbir (.classEq (syn_cfv (syn_cimage R) A) (syn_cima R A)) (syn_wbr A (syn_cimage R) (syn_cima R A)) p0003 p0011
  exact p0012

noncomputable def g_fdpointrelex
    (A : Class) (hyp_fdpointrelex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdpointrel A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cfdpointrel] using (Nominal.classEqRefl (syn_cfdpointrel A)))
  have p0001 :=
    @g_fdmemex
  have p0002 :=
    @g_kqrelex (syn_cfdmem) p0001
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_uniex A hyp_fdpointrelex_1
  have p0005 :=
    @g_pw1ex (syn_cuni A) p0004
  have p0006 :=
    @g_pw1ex (syn_cpw1 (syn_cuni A)) p0005
  have p0007 :=
    @g_xpex (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))) p0003 p0006
  have p0008 :=
    @g_inex (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) p0002 p0007
  have p0009 :=
    @g_eqeltri (syn_cfdpointrel A) (syn_cin (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))) (syn_cvv) p0000 p0008
  exact p0009

noncomputable def g_fdglobalrowex
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdglobalrowex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdglobalrowex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdglobalrowex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdglobalrowmap R A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_u_ne_d : u ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_u : d ≠ u :=
    Ne.symm fresh_u_ne_d
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint (A).fv ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (A).fv ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (A).fv from (by exact fresh_u_not_A))))))
  have dv_cache_0008 : Disjoint (A).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (A).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (A).fv from (by exact fresh_d_not_A))))))
  have dv_cache_0009 : Disjoint (B).fv ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint (B).fv ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (B).fv from (by exact fresh_u_not_B))))))
  have dv_cache_0010 : Disjoint (B).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint (B).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (B).fv from (by exact fresh_d_not_B))))))
  have dv_cache_0011 : Disjoint ((Class.cv u)).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint ((Class.cv u)).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (u), NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)]; exact (show Disjoint (({u} : Finset Var)) (({d} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show u ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ d from (by exact fresh_u_ne_d))))))))
  have dv_cache_0012 : Disjoint ((Class.cv u)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint ((Class.cv u)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({u} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show u ∉ (R).fv from (by exact fresh_u_not_R))))))
  have dv_cache_0013 : Disjoint ((Class.cv d)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show Disjoint ((Class.cv d)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({d} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show d ∉ (R).fv from (by exact fresh_d_not_R))))))
  have dv_cache_0014 : u ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : u ∉ ((syn_cfdrowrel R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, fresh_u_not_B, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : d ∉ ((syn_cfdrowrel R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : d ∉ ((syn_cfdrowfib R A B (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_ne_u, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : u ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show u ≠ d from (by exact fresh_u_ne_d))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdglobalrowmap u A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_iftrue (syn_wbr R (syn_cwe) A) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0)
  have p0002 :=
    @g_vex d
  have p0003 :=
    @g_elfdrowfibg A B (.cv u) (.cv d) R dv_cache_0001 dv_cache_0007 dv_cache_0008 dv_cache_0002 dv_cache_0009 dv_cache_0010 dv_cache_0004 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_bicomi (.classMem (.cv d) (syn_cfdrowfib R A B (.cv u))) (.classMem (syn_cop (syn_csn (.cv d)) (.cv u)) (syn_cfdrowrel R A B)) p0004
  have p0006 :=
    @g_releqmpt u d (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowrel R A B) (syn_cfdrowfib R A B (.cv u)) dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0005
  have p0007 :=
    @g_a1i (.classEq (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))))) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))) (syn_wbr R (syn_cwe) A) p0006
  have p0008 :=
    @g_uniex A hyp_fdglobalrowex_2
  have p0009 :=
    @g_pw1ex (syn_cuni A) p0008
  have p0010 :=
    @g_pw1ex (syn_cpw1 (syn_cuni A)) p0009
  have p0011 :=
    @g_a1i (.classMem (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0010
  have p0012 :=
    @g_vvex
  have p0013 :=
    @g_a1i (.classMem (syn_cvv) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0012
  have p0014 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (.classMem (syn_cvv) (syn_cvv)) p0011 p0013
  have p0015 :=
    @g_xpexg (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0016 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (.classMem (syn_cvv) (syn_cvv))) (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_ssetex
  have p0018 :=
    @g_ins3ex (syn_csset) p0017
  have p0019 :=
    @g_a1i (.classMem (syn_cins3 (syn_csset)) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0018
  have p0020 :=
    @g_fdrowrelex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0004 hyp_fdglobalrowex_1 hyp_fdglobalrowex_2 hyp_fdglobalrowex_3
  have p0021 :=
    @g_ins2exg (syn_cfdrowrel R A B) (syn_cvv)
  have p0022 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrowrel R A B) (syn_cvv)) (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cins3 (syn_csset)) (syn_cvv)) (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)) p0019 p0022
  have p0024 :=
    @g_symdifexg (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (syn_cins3 (syn_csset)) (syn_cvv)) (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv))) (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_n_1cex
  have p0027 :=
    @g_a1i (.classMem (syn_c1c) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0026
  have p0028 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_cvv)) (.classMem (syn_c1c) (syn_cvv)) p0025 p0027
  have p0029 :=
    @g_imaexg (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c) (syn_cvv) (syn_cvv)
  have p0030 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_cvv)) (.classMem (syn_c1c) (syn_cvv))) (.classMem (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)) (syn_cvv)) p0028 p0029
  have p0031 :=
    @g_complexg (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)) (syn_cvv)
  have p0032 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)) (syn_cvv)) (.classMem (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))) (syn_cvv)) p0030 p0031
  have p0033 :=
    @g_cnvexg (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))) (syn_cvv)
  have p0034 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))) (syn_cvv)) (.classMem (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))) (syn_cvv)) p0032 p0033
  have p0035 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_cvv)) (.classMem (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))) (syn_cvv)) p0016 p0034
  have p0036 :=
    @g_inexg (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))) (syn_cvv) (syn_cvv)
  have p0037 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_cvv)) (.classMem (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))) (syn_cvv))) (.classMem (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))))) (syn_cvv)) p0035 p0036
  have p0038 :=
    @g_eqeltrrd (syn_wbr R (syn_cwe) A) (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))))) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cvv) p0007 p0037
  have p0039 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A) (syn_cif (syn_wbr R (syn_cwe) A) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0)) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cvv) p0001 p0038
  have p0040 :=
    @g_iffalse (syn_wbr R (syn_cwe) A) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0)
  have p0041 :=
    @g_n_0ex
  have p0042 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv)) (.neg (syn_wbr R (syn_cwe) A)) p0041
  have p0043 :=
    @g_eqeltrd (.neg (syn_wbr R (syn_cwe) A)) (syn_cif (syn_wbr R (syn_cwe) A) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0)) (syn_c0) (syn_cvv) p0040 p0042
  have p0044 :=
    @g_pm2_61i (syn_wbr R (syn_cwe) A) (.classMem (syn_cif (syn_wbr R (syn_cwe) A) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0)) (syn_cvv)) p0039 p0043
  have p0045 :=
    @g_eqeltri (syn_cfdglobalrowmap R A B) (syn_cif (syn_wbr R (syn_cwe) A) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0)) (syn_cvv) p0000 p0044
  exact p0045

noncomputable def g_fdglobalrowval
    (u : Var) (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_u : u ∉ A.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (.classEq (syn_cfdglobalrowmap R A B) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdglobalrowmap u A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_a1i (.classEq (syn_cfdglobalrowmap R A B) (syn_cif (syn_wbr R (syn_cwe) A) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0))) (syn_wbr R (syn_cwe) A) p0000
  have p0002 :=
    @g_iftrue (syn_wbr R (syn_cwe) A) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0)
  have p0003 :=
    @g_eqtrd (syn_wbr R (syn_cwe) A) (syn_cfdglobalrowmap R A B) (syn_cif (syn_wbr R (syn_cwe) A) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0)) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) p0001 p0002
  exact p0003

#print axioms g_fdglobalrowval

end NFChoice.DirectNominalPrf.WPPReplay
