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
import NominalWPPReplayChunk014Compact001Part022

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

noncomputable def g_fdcodemap2ex
    (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) (hyp_fdcodemap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcodemap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcodemap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_fdcodemap2ex_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcodemap2 R A B C) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_C : u ∉ C.fv := by
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
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_C : d ∉ C.fv := by
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
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0009 : u ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : Disjoint (A).fv ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint (A).fv ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (A).fv from (by exact fresh_u_not_A))))))
  have dv_cache_0012 : Disjoint (A).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint (A).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (A).fv from (by exact fresh_d_not_A))))))
  have dv_cache_0013 : Disjoint (B).fv ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show Disjoint (B).fv ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (B).fv from (by exact fresh_u_not_B))))))
  have dv_cache_0014 : Disjoint (B).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show Disjoint (B).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (B).fv from (by exact fresh_d_not_B))))))
  have dv_cache_0015 : Disjoint ((Class.cv u)).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show Disjoint ((Class.cv u)).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (u), NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)]; exact (show Disjoint (({u} : Finset Var)) (({d} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show u ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ d from (by exact fresh_u_ne_d))))))))
  have dv_cache_0016 : Disjoint ((Class.cv u)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show Disjoint ((Class.cv u)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({u} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show u ∉ (R).fv from (by exact fresh_u_not_R))))))
  have dv_cache_0017 : Disjoint ((Class.cv d)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show Disjoint ((Class.cv d)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({d} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show d ∉ (R).fv from (by exact fresh_d_not_R))))))
  have dv_cache_0018 : u ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : u ∉ ((syn_cfdrowrel R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, fresh_u_not_B, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : d ∉ ((syn_cfdrowrel R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : d ∉ ((syn_cfdrowfib R A B (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_ne_u, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : u ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show u ≠ d from (by exact fresh_u_ne_d))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdcodemap2 u A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_a1i (.classEq (syn_cfdcodemap2 R A B C) (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u)))) (syn_wbr R (syn_cwe) A) p0000
  have p0002 :=
    @g_vex d
  have p0003 :=
    @g_elfdrowfibg A B (.cv u) (.cv d) R dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0003 dv_cache_0013 dv_cache_0014 dv_cache_0006 dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_bicomi (.classMem (.cv d) (syn_cfdrowfib R A B (.cv u))) (.classMem (syn_cop (syn_csn (.cv d)) (.cv u)) (syn_cfdrowrel R A B)) p0004
  have p0006 :=
    @g_releqmpt u d (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowrel R A B) (syn_cfdrowfib R A B (.cv u)) dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 p0005
  have p0007 :=
    @g_a1i (.classEq (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))))) (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u)))) (syn_wbr R (syn_cwe) A) p0006
  have p0008 :=
    @g_pw1ex C hyp_fdcodemap2ex_4
  have p0009 :=
    @g_pw1ex (syn_cpw1 C) p0008
  have p0010 :=
    @g_a1i (.classMem (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0009
  have p0011 :=
    @g_vvex
  have p0012 :=
    @g_a1i (.classMem (syn_cvv) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0011
  have p0013 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (.classMem (syn_cvv) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_xpexg (syn_cpw1 (syn_cpw1 C)) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (.classMem (syn_cvv) (syn_cvv))) (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_ssetex
  have p0017 :=
    @g_ins3ex (syn_csset) p0016
  have p0018 :=
    @g_a1i (.classMem (syn_cins3 (syn_csset)) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0017
  have p0019 :=
    @g_fdrowrelex2 A B R dv_cache_0001 dv_cache_0003 dv_cache_0006 hyp_fdcodemap2ex_1 hyp_fdcodemap2ex_2 hyp_fdcodemap2ex_3
  have p0020 :=
    @g_ins2exg (syn_cfdrowrel R A B) (syn_cvv)
  have p0021 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrowrel R A B) (syn_cvv)) (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cins3 (syn_csset)) (syn_cvv)) (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)) p0018 p0021
  have p0023 :=
    @g_symdifexg (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (syn_cins3 (syn_csset)) (syn_cvv)) (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv))) (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_cvv)) p0022 p0023
  have p0025 :=
    @g_n_1cex
  have p0026 :=
    @g_a1i (.classMem (syn_c1c) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0025
  have p0027 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_cvv)) (.classMem (syn_c1c) (syn_cvv)) p0024 p0026
  have p0028 :=
    @g_imaexg (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c) (syn_cvv) (syn_cvv)
  have p0029 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_cvv)) (.classMem (syn_c1c) (syn_cvv))) (.classMem (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)) (syn_cvv)) p0027 p0028
  have p0030 :=
    @g_complexg (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)) (syn_cvv)
  have p0031 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)) (syn_cvv)) (.classMem (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))) (syn_cvv)) p0029 p0030
  have p0032 :=
    @g_cnvexg (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))) (syn_cvv)
  have p0033 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))) (syn_cvv)) (.classMem (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))) (syn_cvv)) p0031 p0032
  have p0034 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_cvv)) (.classMem (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))) (syn_cvv)) p0015 p0033
  have p0035 :=
    @g_inexg (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))) (syn_cvv) (syn_cvv)
  have p0036 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_cvv)) (.classMem (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))) (syn_cvv))) (.classMem (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))))) (syn_cvv)) p0034 p0035
  have p0037 :=
    @g_eqeltrrd (syn_wbr R (syn_cwe) A) (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))))) (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))) (syn_cvv) p0007 p0036
  have p0038 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A) (syn_cfdcodemap2 R A B C) (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))) (syn_cvv) p0001 p0037
  exact p0038

noncomputable def g_fdcodeeqrnmap2
    (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.classEq (syn_cfdcode R A B C) (syn_crn (syn_cfdcodemap2 R A B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_q_ne_x : q ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_u : q ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0007 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : q ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0011 : q ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : q ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have dv_cache_0016 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : u ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_cfdrowfib R A B (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, fresh_q_ne_u, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : u ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show u ≠ q from (by exact fresh_u_ne_q))
  have dv_cache_0023 : x ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((Wff.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_q, fresh_x_not_A, fresh_x_not_B, fresh_x_ne_u, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : x ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have dv_cache_0026 : Disjoint (A).fv ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (show Disjoint (A).fv ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (A).fv from (by exact fresh_u_not_A))))))
  have dv_cache_0027 : Disjoint (A).fv ((syn_csn (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show Disjoint (A).fv ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((A).fv) (((syn_csn (.cv x))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((A).fv) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact fresh_x_not_A))))))))))
  have dv_cache_0028 : Disjoint (B).fv ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show Disjoint (B).fv ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (B).fv from (by exact fresh_u_not_B))))))
  have dv_cache_0029 : Disjoint (B).fv ((syn_csn (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show Disjoint (B).fv ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((B).fv) (((syn_csn (.cv x))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((B).fv) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))))
  have dv_cache_0030 : Disjoint ((Class.cv u)).fv ((syn_csn (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show Disjoint ((Class.cv u)).fv ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (({u} : Finset Var)) (((syn_csn (.cv x))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (({u} : Finset Var)) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({u} : Finset Var)) (({x} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show u ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ x from (by exact fresh_u_ne_x))))))))))))
  have dv_cache_0031 : Disjoint ((Class.cv u)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show Disjoint ((Class.cv u)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({u} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show u ∉ (R).fv from (by exact fresh_u_not_R))))))
  have dv_cache_0032 : Disjoint ((syn_csn (syn_csn (.cv x)))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show Disjoint ((syn_csn (syn_csn (.cv x)))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (((syn_csn (.cv x))).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (((Class.cv x)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))))))
  have dv_cache_0033 : u ∉ ((syn_csn (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : u ∉ ((Wff.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, fresh_u_not_B, fresh_u_ne_x, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : Disjoint (A).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show Disjoint (A).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0036 : Disjoint (B).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show Disjoint (B).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (B).fv from (by exact fresh_x_not_B))))))
  have dv_cache_0037 : Disjoint ((Class.cv x)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdcode x A B C R q dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdcodemap2 u A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0016 dv_cache_0006 dv_cache_0007 dv_cache_0017 dv_cache_0010 dv_cache_0018 dv_cache_0019
  have p0002 :=
    @g_rnmpt u q (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u)) (syn_cfdcodemap2 R A B C) dv_cache_0020 dv_cache_0021 dv_cache_0022 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))))
  have p0004 :=
    @g_elpw12 x (.cv u) C dv_cache_0023 dv_cache_0012
  have p0005 :=
    @g_anbi1i (.classMem (.cv u) (syn_cpw1 (syn_cpw1 C))) (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))) p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv u) (syn_cpw1 (syn_cpw1 C))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) u p0005
  have p0007 :=
    @g_bitri (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) (syn_wex u (syn_wa (.classMem (.cv u) (syn_cpw1 (syn_cpw1 C))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))) (syn_wex u (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))) p0003 p0006
  have p0008 :=
    @g_r19_41v (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))) x C dv_cache_0024
  have p0009 :=
    @g_bicomi (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))) (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) p0008
  have p0010 :=
    @g_exbii (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))) u p0009
  have p0011 :=
    @g_bitri (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) (syn_wex u (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))) (syn_wex u (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))) p0007 p0010
  have p0012 :=
    @g_rexcom4 (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) x u C dv_cache_0018 dv_cache_0025
  have p0013 :=
    @g_bicomi (syn_wrex x C (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))) (syn_wex u (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))) p0012
  have p0014 :=
    @g_bitri (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) (syn_wex u (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))) (syn_wrex x C (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))) p0011 p0013
  have p0015 :=
    @g_snex (syn_csn (.cv x))
  have p0016 :=
    @g_fdrowfibeq4 A B (.cv u) (syn_csn (syn_csn (.cv x))) R dv_cache_0001 dv_cache_0026 dv_cache_0027 dv_cache_0003 dv_cache_0028 dv_cache_0029 dv_cache_0007 dv_cache_0030 dv_cache_0031 dv_cache_0032
  have p0017 :=
    @g_eqeq2d (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (syn_cfdrowfib R A B (.cv u)) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x)))) (.cv q) p0016
  have p0018 :=
    @g_ceqsexv (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))) (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x))))) u (syn_csn (syn_csn (.cv x))) dv_cache_0033 dv_cache_0034 p0015 p0017
  have p0019 :=
    @g_rexbii (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))) (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x))))) x C p0018
  have p0020 :=
    @g_bitri (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) (syn_wrex x C (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))) (syn_wrex x C (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x)))))) p0014 p0019
  have p0021 :=
    @g_vex x
  have p0022 :=
    @g_fdrowfibsn2 A B (.cv x) R dv_cache_0001 dv_cache_0035 dv_cache_0003 dv_cache_0036 dv_cache_0007 dv_cache_0037 p0021
  have p0023 :=
    @g_eqeq2i (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x)))) (syn_cfdrow R A B (.cv x)) (.cv q) p0022
  have p0024 :=
    @g_rexbii (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x))))) (.classEq (.cv q) (syn_cfdrow R A B (.cv x))) x C p0023
  have p0025 :=
    @g_bitri (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) (syn_wrex x C (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x)))))) (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))) p0020 p0024
  have p0026 :=
    @g_abbii (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))) (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))) q p0025
  have p0027 :=
    @g_eqtri (syn_crn (syn_cfdcodemap2 R A B C)) (.cab q (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))) (.cab q (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x))))) p0002 p0026
  have p0028 :=
    @g_eqtr4i (syn_cfdcode R A B C) (.cab q (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x))))) (syn_crn (syn_cfdcodemap2 R A B C)) p0000 p0027
  exact p0028

noncomputable def g_fdcodeex2
    (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) (hyp_fdcodeex2_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcodeex2_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcodeex2_3 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_fdcodeex2_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcode R A B C) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0005 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @g_fdcodeeqrnmap2 A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_a1i (.classEq (syn_cfdcode R A B C) (syn_crn (syn_cfdcodemap2 R A B C))) (syn_wbr R (syn_cwe) A) p0000
  have p0002 :=
    @g_fdcodemap2ex A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_fdcodeex2_1 hyp_fdcodeex2_2 hyp_fdcodeex2_3 hyp_fdcodeex2_4
  have p0003 :=
    @g_rnexg (syn_cfdcodemap2 R A B C) (syn_cvv)
  have p0004 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcodemap2 R A B C) (syn_cvv)) (.classMem (syn_crn (syn_cfdcodemap2 R A B C)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A) (syn_cfdcode R A B C) (syn_crn (syn_cfdcodemap2 R A B C)) (syn_cvv) p0001 p0004
  exact p0005

noncomputable def g_fdcodeelpwpw2
    (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) (hyp_fdcodeelpwpw2_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcodeelpwpw2_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcodeelpwpw2_3 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_fdcodeelpwpw2_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcode R A B C) (syn_cpw (syn_cpw (syn_cfdif R A B))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0005 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @g_fdcodesspw2 A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_a1i (syn_wss (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B))) (syn_wbr R (syn_cwe) A) p0000
  have p0002 :=
    @g_fdcodeex2 A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_fdcodeelpwpw2_1 hyp_fdcodeelpwpw2_2 hyp_fdcodeelpwpw2_3 hyp_fdcodeelpwpw2_4
  have p0003 :=
    @g_elpwg (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B)) (syn_cvv)
  have p0004 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcode R A B C) (syn_cvv)) (syn_wb (.classMem (syn_cfdcode R A B C) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wss (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B)))) p0002 p0003
  have p0005 :=
    @g_mpbird (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcode R A B C) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wss (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B))) p0001 p0004
  exact p0005

#print axioms g_fdcodeelpwpw2

end NFChoice.DirectNominalPrf.WPPReplay
