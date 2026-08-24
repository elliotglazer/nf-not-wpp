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
import NominalWPPReplayChunk014Compact001Part014

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

noncomputable def g_fdminvalpfpivred
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  let c : Var := freshVar proofSupport 1
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d_ne_c : d ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_c_ne_d : c ≠ d :=
    Ne.symm fresh_d_ne_c
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((syn_copk C D)).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv ((syn_copk C D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((A).fv) (((C).fv) ∪ ((D).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (A).fv (C).fv from (by exact dv_A_C)), (show Disjoint (A).fv (D).fv from (by exact dv_A_D))⟩))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv ((syn_copk C D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((B).fv) (((C).fv) ∪ ((D).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (B).fv (C).fv from (by exact dv_B_C)), (show Disjoint (B).fv (D).fv from (by exact dv_B_D))⟩))))
  have dv_cache_0006 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : Disjoint ((syn_copk C D)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint ((syn_copk C D)).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint (((C).fv) ∪ ((D).fv)) ((R).fv) from (Finset.disjoint_union_left.mpr ⟨(show Disjoint (C).fv (R).fv from (by exact dv_C_R)), (show Disjoint (D).fv (R).fv from (by exact dv_D_R))⟩))))
  have dv_cache_0009 : d ∉ ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_C, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0012 : Disjoint (A).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0013 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0014 : Disjoint (B).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0015 : Disjoint (C).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0016 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0017 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0019 : d ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : c ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : c ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : c ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : c ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : c ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0025 : d ∉ ((syn_cfdminvalp R A B (syn_copk C D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_not_C, fresh_d_not_D, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : d ∉ ((syn_cfpiv R A C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_C, fresh_d_not_D, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : d ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, fresh_d_not_A, fresh_d_not_C, fresh_d_not_B, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_opkex C D
  have p0001 :=
    @g_elfdminvalp A B (syn_copk C D) R d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0000
  have p0002 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_cfdminvalp R A B (syn_copk C D))) (syn_wa (.classMem (.cv d) A) (.classMem (syn_copk (syn_csn (.cv d)) (syn_copk C D)) (syn_cfdminsep R A B)))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) p0001
  have p0003 :=
    @g_fdminsepfpivred A B C D R d dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0003 dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0006 dv_cache_0007 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0010
  have p0004 :=
    @g_anbi2d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_copk (syn_csn (.cv d)) (syn_copk C D)) (syn_cfdminsep R A B)) (.classMem (.cv d) (syn_cfpiv R A C D)) (.classMem (.cv d) A) p0003
  have p0005 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (.cv d) (syn_cfdminvalp R A B (syn_copk C D))) (syn_wa (.classMem (.cv d) A) (.classMem (syn_copk (syn_csn (.cv d)) (syn_copk C D)) (syn_cfdminsep R A B))) (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D))) p0002 p0004
  have p0006 :=
    @g_simpr (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D))
  have p0007 :=
    @g_elfpiv A C D R d c dv_cache_0011 dv_cache_0012 dv_cache_0003 dv_cache_0020 dv_cache_0004 dv_cache_0015 dv_cache_0016 dv_cache_0021 dv_cache_0017 dv_cache_0018 dv_cache_0022 dv_cache_0019 dv_cache_0023 dv_cache_0010 dv_cache_0024
  have p0008 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 C D))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv d) R (.cv c))))) p0007
  have p0009 :=
    @g_simpll (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 C D)) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv d) R (.cv c))))
  have p0010 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 C D))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv d) R (.cv c))))) (.classMem (.cv d) A) p0008 p0009
  have p0011 :=
    @g_id (.classMem (.cv d) (syn_cfpiv R A C D))
  have p0012 :=
    @g_jca (.classMem (.cv d) (syn_cfpiv R A C D)) (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D)) p0010 p0011
  have p0013 :=
    @g_impbii (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D))) (.classMem (.cv d) (syn_cfpiv R A C D)) p0006 p0012
  have p0014 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D))) (.classMem (.cv d) (syn_cfpiv R A C D))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) p0013
  have p0015 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (.cv d) (syn_cfdminvalp R A B (syn_copk C D))) (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D))) (.classMem (.cv d) (syn_cfpiv R A C D)) p0005 p0014
  have p0016 :=
    @g_eqrdv (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) d (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D) dv_cache_0025 dv_cache_0026 dv_cache_0027 p0015
  exact p0016

noncomputable def g_fdminvalpeq4
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf (.imp (.classEq C D) (.classEq (syn_cfdminvalp R A B C) (syn_cfdminvalp R A B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cfdminvalp] using (Nominal.classEqRefl (syn_cfdminvalp R A B C)))
  have p0001 :=
    @g_a1i (.classEq (syn_cfdminvalp R A B C) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)))) (.classEq C D) p0000
  have p0002 :=
    (by simpa [syn_cuni1] using (Nominal.classEqRefl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)))))
  have p0003 :=
    @g_a1i (.classEq (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (syn_cuni (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) (syn_c1c)))) (.classEq C D) p0002
  have p0004 :=
    @g_sneq C D
  have p0005 :=
    @g_imakeq2d (.classEq C D) (syn_csn C) (syn_csn D) (syn_ccnvk (syn_cfdminsep R A B)) p0004
  have p0006 :=
    @g_ineq1d (.classEq C D) (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c) p0005
  have p0007 :=
    @g_unieqd (.classEq C D) (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) (syn_c1c)) (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c)) p0006
  have p0008 :=
    @g_eqtrd (.classEq C D) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (syn_cuni (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) (syn_c1c))) (syn_cuni (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c))) p0003 p0007
  have p0009 :=
    (by simpa [syn_cuni1] using (Nominal.classEqRefl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)))))
  have p0010 :=
    @g_a1i (.classEq (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D))) (syn_cuni (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c)))) (.classEq C D) p0009
  have p0011 :=
    @g_eqtr4d (.classEq C D) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (syn_cuni (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c))) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D))) p0008 p0010
  have p0012 :=
    @g_eqtrd (.classEq C D) (syn_cfdminvalp R A B C) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D))) p0001 p0011
  have p0013 :=
    (by simpa [syn_cfdminvalp] using (Nominal.classEqRefl (syn_cfdminvalp R A B D)))
  have p0014 :=
    @g_a1i (.classEq (syn_cfdminvalp R A B D) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)))) (.classEq C D) p0013
  have p0015 :=
    @g_eqtr4d (.classEq C D) (syn_cfdminvalp R A B C) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D))) (syn_cfdminvalp R A B D) p0012 p0014
  exact p0015

noncomputable def g_fdpivinrange
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) (hyp_fdpivinrange_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdpivinrange_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdpivinrange_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_d_ne_p : d ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_d : p ≠ d :=
    Ne.symm fresh_d_ne_p
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
  have dv_cache_0011 : Disjoint (A).fv ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint (A).fv ((syn_copk C D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((A).fv) (((C).fv) ∪ ((D).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (A).fv (C).fv from (by exact dv_A_C)), (show Disjoint (A).fv (D).fv from (by exact dv_A_D))⟩))))
  have dv_cache_0012 : Disjoint (B).fv ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint (B).fv ((syn_copk C D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((B).fv) (((C).fv) ∪ ((D).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (B).fv (C).fv from (by exact dv_B_C)), (show Disjoint (B).fv (D).fv from (by exact dv_B_D))⟩))))
  have dv_cache_0013 : Disjoint ((syn_copk C D)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show Disjoint ((syn_copk C D)).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint (((C).fv) ∪ ((D).fv)) ((R).fv) from (Finset.disjoint_union_left.mpr ⟨(show Disjoint (C).fv (R).fv from (by exact dv_C_R)), (show Disjoint (D).fv (R).fv from (by exact dv_D_R))⟩))))
  have dv_cache_0014 : Disjoint (A).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show Disjoint (A).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0015 : Disjoint (B).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show Disjoint (B).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0016 : Disjoint ((Class.cv p)).fv ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show Disjoint ((Class.cv p)).fv ((syn_copk C D)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint (({p} : Finset Var)) (((C).fv) ∪ ((D).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({p} : Finset Var)) ((C).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (C).fv from (by exact fresh_p_not_C)))), (show Disjoint (({p} : Finset Var)) ((D).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (D).fv from (by exact fresh_p_not_D))))⟩))))
  have dv_cache_0017 : Disjoint ((Class.cv p)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show Disjoint ((Class.cv p)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0018 : p ∉ ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_C, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((syn_cxpk B B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : p ∉ ((Wff.classEq (syn_cfdminvalp R A B (syn_copk C D)) (.cv d))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, fresh_p_not_C, fresh_p_not_D, fresh_p_not_R, fresh_p_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : Disjoint (A).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show Disjoint (A).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (A).fv from (by exact fresh_d_not_A))))))
  have dv_cache_0022 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : Disjoint (B).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show Disjoint (B).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (B).fv from (by exact fresh_d_not_B))))))
  have dv_cache_0024 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : Disjoint ((Class.cv d)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show Disjoint ((Class.cv d)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({d} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show d ∉ (R).fv from (by exact fresh_d_not_R))))))
  have dv_cache_0026 : p ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : d ∉ ((syn_cfpiv R A C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_C, fresh_d_not_D, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : d ∉ ((Wff.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, fresh_d_not_A, fresh_d_not_C, fresh_d_not_B, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdminvalpfpivred A B C D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_fdminvalpex A B (syn_copk C D) R dv_cache_0001 dv_cache_0011 dv_cache_0004 dv_cache_0012 dv_cache_0007 dv_cache_0013 hyp_fdpivinrange_1 hyp_fdpivinrange_2 hyp_fdpivinrange_3
  have p0002 :=
    @g_a1i (.classMem (syn_cfdminvalp R A B (syn_copk C D)) (syn_cvv)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) p0001
  have p0003 :=
    @g_eqeltrrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D) (syn_cvv) p0000 p0002
  have p0004 :=
    @g_simpr (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
  have p0005 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))
  have p0006 :=
    @g_id (syn_wa (.classMem C B) (.classMem D B))
  have p0007 :=
    @g_simpl (.classMem C B) (.classMem D B)
  have p0008 :=
    @g_elex C B
  have p0009 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem C B) (.classMem C (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_simpr (.classMem C B) (.classMem D B)
  have p0011 :=
    @g_elex D B
  have p0012 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem D B) (.classMem D (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_jca (syn_wa (.classMem C B) (.classMem D B)) (.classMem C (syn_cvv)) (.classMem D (syn_cvv)) p0009 p0012
  have p0014 :=
    @g_opkelxpkg C D B B (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (.classMem (syn_copk C D) (syn_cxpk B B)) (syn_wa (.classMem C B) (.classMem D B))) p0013 p0014
  have p0016 :=
    @g_mpbird (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk C D) (syn_cxpk B B)) (syn_wa (.classMem C B) (.classMem D B)) p0006 p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk C D) (syn_cxpk B B)) p0005 p0016
  have p0018 :=
    @g_syl (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_copk C D) (syn_cxpk B B)) p0004 p0017
  have p0019 :=
    @g_simpr (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
  have p0020 :=
    @g_fdminvalpfpivred A B C D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0021 :=
    @g_syl (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D)) p0019 p0020
  have p0022 :=
    @g_simpl (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
  have p0023 :=
    @g_eqcomd (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))) (.cv d) (syn_cfpiv R A C D) p0022
  have p0024 :=
    @g_eqtrd (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))) (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D) (.cv d) p0021 p0023
  have p0025 :=
    @g_jca (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))) (.classMem (syn_copk C D) (syn_cxpk B B)) (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (.cv d)) p0018 p0024
  have p0026 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk C D) R dv_cache_0001 dv_cache_0014 dv_cache_0011 dv_cache_0004 dv_cache_0015 dv_cache_0012 dv_cache_0007 dv_cache_0016 dv_cache_0017 dv_cache_0013
  have p0027 :=
    @g_eqeq1d (.classEq (.cv p) (syn_copk C D)) (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk C D)) (.cv d) p0026
  have p0028 :=
    @g_rspcev (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv d)) (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (.cv d)) p (syn_copk C D) (syn_cxpk B B) dv_cache_0018 dv_cache_0019 dv_cache_0020 p0027
  have p0029 :=
    @g_syl (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))) (syn_wa (.classMem (syn_copk C D) (syn_cxpk B B)) (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (.cv d))) (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv d))) p0025 p0028
  have p0030 :=
    @g_fdpivrange2br A B (.cv d) R p dv_cache_0001 dv_cache_0021 dv_cache_0004 dv_cache_0022 dv_cache_0023 dv_cache_0007 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 hyp_fdpivinrange_1 hyp_fdpivinrange_2 hyp_fdpivinrange_3
  have p0031 :=
    @g_sylibr (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))) (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv d))) (.classMem (.cv d) (syn_cfdpivrange2 R A B)) p0029 p0030
  have p0032 :=
    @g_simpl (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
  have p0033 :=
    @g_eleq1d (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))) (.cv d) (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B) p0032
  have p0034 :=
    @g_mpbid (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))) (.classMem (.cv d) (syn_cfdpivrange2 R A B)) (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)) p0031 p0033
  have p0035 :=
    @g_ex (.classEq (.cv d) (syn_cfpiv R A C D)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)) p0034
  have p0036 :=
    @g_vtocleg (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B))) d (syn_cfpiv R A C D) (syn_cvv) dv_cache_0028 dv_cache_0029 p0035
  have p0037 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_cfpiv R A C D) (syn_cvv)) (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B))) p0003 p0036
  have p0038 :=
    @g_pm2_43i (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)) p0037
  exact p0038

#print axioms g_fdpivinrange

end NFChoice.DirectNominalPrf.WPPReplay
