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
import NominalWPPReplayChunk014Compact001Part028

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

noncomputable def g_fdcolcodemapf12
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdcolcodemapf12_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcolcodemapf12_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcolcodemapf12_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_q_ne_r : q ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0004 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : r ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((A).fv) (((syn_cuni (.cv q))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((A).fv) (((Class.cv q)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({q} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show q ∉ (A).fv from (by exact fresh_q_not_A))))))))))
  have dv_cache_0011 : Disjoint (A).fv ((syn_cuni (syn_cuni (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint (A).fv ((syn_cuni (syn_cuni (.cv r)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((A).fv) (((syn_cuni (.cv r))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((A).fv) (((Class.cv r)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({r} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show r ∉ (A).fv from (by exact fresh_r_not_A))))))))))
  have dv_cache_0012 : Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((B).fv) (((syn_cuni (.cv q))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((B).fv) (((Class.cv q)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({q} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show q ∉ (B).fv from (by exact fresh_q_not_B))))))))))
  have dv_cache_0013 : Disjoint (B).fv ((syn_cuni (syn_cuni (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show Disjoint (B).fv ((syn_cuni (syn_cuni (.cv r)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((B).fv) (((syn_cuni (.cv r))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((B).fv) (((Class.cv r)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({r} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show r ∉ (B).fv from (by exact fresh_r_not_B))))))))))
  have dv_cache_0014 : Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv ((syn_cuni (syn_cuni (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv ((syn_cuni (syn_cuni (.cv r)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni ((syn_cuni (.cv q))), NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni ((syn_cuni (.cv r)))]; exact (show Disjoint (((syn_cuni (.cv q))).fv) (((syn_cuni (.cv r))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv q)).fv) (((syn_cuni (.cv r))).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) (((syn_cuni (.cv r))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (({q} : Finset Var)) (((Class.cv r)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) (({r} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show q ∉ ({r} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ r from (by exact fresh_q_ne_r))))))))))))))))
  have dv_cache_0015 : Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((syn_cuni (.cv q))).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv q)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show q ∉ (R).fv from (by exact fresh_q_not_R))))))))))
  have dv_cache_0016 : Disjoint ((syn_cuni (syn_cuni (.cv r)))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show Disjoint ((syn_cuni (syn_cuni (.cv r)))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((syn_cuni (.cv r))).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv r)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({r} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show r ∉ (R).fv from (by exact fresh_r_not_R))))))))))
  have dv_cache_0017 : r ∉ ((syn_cpw1 (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : q ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, fresh_q_not_A, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : r ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, fresh_r_not_A, fresh_r_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0021 : q ∉ ((syn_cpw1 (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : q ∉ ((syn_cfdcolcodemap R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : r ∉ ((syn_cfdcolcodemap R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_not_B, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0001 :=
    @g_fdcolcodemapf A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapf12_1 hyp_fdcolcodemapf12_2 hyp_fdcolcodemapf12_3
  have p0002 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A) (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0004 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0005 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0003 p0004
  have p0006 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0007 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0008 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) p0007 p0008
  have p0010 :=
    @g_fdcolcodearg A q dv_cache_0004
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0009 p0010
  have p0012 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (.classMem (syn_cuni (syn_cuni (.cv q))) A) p0011 p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classMem (syn_cuni (syn_cuni (.cv q))) A) p0006 p0013
  have p0015 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0016 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0017 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))) p0016 p0017
  have p0019 :=
    @g_fdcolcodearg A r dv_cache_0005
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) A) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))) p0018 p0019
  have p0021 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv r))) A) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) A) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))) (.classMem (syn_cuni (syn_cuni (.cv r))) A) p0020 p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classMem (syn_cuni (syn_cuni (.cv r))) A) p0015 p0022
  have p0024 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classMem (syn_cuni (syn_cuni (.cv r))) A) p0014 p0023
  have p0025 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classMem (syn_cuni (syn_cuni (.cv r))) A)) p0005 p0024
  have p0026 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0027 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0028 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0029 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0030 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A) p0028 p0029
  have p0031 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0032 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) p0031 p0032
  have p0034 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) p0030 p0033
  have p0035 :=
    @g_fdcolcodemapval A B R q dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0003 dv_cache_0006 dv_cache_0007 hyp_fdcolcodemapf12_1 hyp_fdcolcodemapf12_2 hyp_fdcolcodemapf12_3
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))) p0034 p0035
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))) p0027 p0036
  have p0038 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0039 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0040 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A) p0039 p0040
  have p0042 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0043 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))) p0042 p0043
  have p0045 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wbr R (syn_cwe) A) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))) p0041 p0044
  have p0046 :=
    @g_fdcolcodemapval A B R r dv_cache_0001 dv_cache_0002 dv_cache_0005 dv_cache_0003 dv_cache_0008 dv_cache_0009 hyp_fdcolcodemapf12_1 hyp_fdcolcodemapf12_2 hyp_fdcolcodemapf12_3
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r))))) p0045 p0046
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r))))) p0038 p0047
  have p0049 :=
    @g_n_3eqtr3d (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r)))) p0026 p0037 p0048
  have p0050 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classMem (syn_cuni (syn_cuni (.cv r))) A))) (.classEq (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r))))) p0025 p0049
  have p0051 :=
    @g_fdcodeinj2 A B (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) R dv_cache_0001 dv_cache_0010 dv_cache_0011 dv_cache_0002 dv_cache_0012 dv_cache_0013 dv_cache_0003 dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_fdcolcodemapf12_1 hyp_fdcolcodemapf12_2 hyp_fdcolcodemapf12_3
  have p0052 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classMem (syn_cuni (syn_cuni (.cv r))) A))) (.classEq (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r)))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r)))) p0050 p0051
  have p0053 :=
    @g_sneqd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) p0052
  have p0054 :=
    @g_sneqd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (.cv r)))) p0053
  have p0055 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0056 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0057 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))
  have p0058 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) p0056 p0057
  have p0059 :=
    @g_fdcolcodearg A q dv_cache_0004
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0058 p0059
  have p0061 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0062 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0060 p0061
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0055 p0062
  have p0064 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0065 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0066 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))
  have p0067 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))) p0065 p0066
  have p0068 :=
    @g_fdcolcodearg A r dv_cache_0005
  have p0069 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) A) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))) p0067 p0068
  have p0070 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (.cv r))) A) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) A) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0069 p0070
  have p0072 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0064 p0071
  have p0073 :=
    @g_n_3eqtr4d (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) (.cv q) (.cv r) p0054 p0063 p0072
  have p0074 :=
    @g_ex (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r)) p0073
  have p0075 :=
    @g_ralrimivva (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (.imp (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r))) q r (syn_cpw1 (syn_cpw1 A)) (syn_cpw1 (syn_cpw1 A)) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0074
  have p0076 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wral q (syn_cpw1 (syn_cpw1 A)) (syn_wral r (syn_cpw1 (syn_cpw1 A)) (.imp (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r))))) p0002 p0075
  have p0077 :=
    @g_dff13 q r (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cfdcolcodemap R A B) dv_cache_0021 dv_cache_0017 dv_cache_0022 dv_cache_0023 dv_cache_0020
  have p0078_e00_recanon : Nominal.NPrf (syn_wb (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wa (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wral q (syn_cpw1 (syn_cpw1 A)) (syn_wral r (syn_cpw1 (syn_cpw1 A)) (.imp (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cfdcolcodemap syn_cres syn_cpw1 syn_cpw
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0077
  have p0078 :=
    @g_a1i (syn_wb (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wa (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wral q (syn_cpw1 (syn_cpw1 A)) (syn_wral r (syn_cpw1 (syn_cpw1 A)) (.imp (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r))))))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0078_e00_recanon
  have p0079 :=
    @g_mpbird (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wa (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wral q (syn_cpw1 (syn_cpw1 A)) (syn_wral r (syn_cpw1 (syn_cpw1 A)) (.imp (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r)))))) p0076 p0078
  exact p0079

noncomputable def g_fdcolcodecardle2
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdcolcodecardle2_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcolcodecardle2_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcolcodecardle2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let f : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_f_ne_z : f ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_f : z ≠ f :=
    Ne.symm fresh_f_ne_z
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0004 : f ∉ ((syn_cfdcolcodemap R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, fresh_f_not_B, fresh_f_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, fresh_f_not_B, fresh_f_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : f ∉ ((Wff.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_z, fresh_f_not_A, fresh_f_not_B, fresh_f_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : f ∉ ((syn_cpw1 (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : f ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cpw (syn_cpw (syn_cfdif R A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B))))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_R, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdcolcodemapf12 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodecardle2_1 hyp_fdcolcodecardle2_2 hyp_fdcolcodecardle2_3
  have p0001 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0002 :=
    @g_fdcolcodemapex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodecardle2_1 hyp_fdcolcodecardle2_2 hyp_fdcolcodecardle2_3
  have p0003 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcolcodemap R A B) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))) (.cv f) (syn_cfdcolcodemap R A B)
  have p0005 :=
    @g_spcegv (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) f (syn_cfdcolcodemap R A B) (syn_cvv) dv_cache_0004 dv_cache_0005 p0004
  have p0006 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (.classMem (syn_cfdcolcodemap R A B) (syn_cvv)) (.imp (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))))) p0003 p0005
  have p0007 :=
    @g_mpd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))) p0000 p0006
  have p0008 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0009 :=
    @g_fdifex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodecardle2_1 hyp_fdcolcodecardle2_2 hyp_fdcolcodecardle2_3
  have p0010 :=
    @g_pwexg (syn_cfdif R A B) (syn_cvv)
  have p0011 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdif R A B) (syn_cvv)) (.classMem (syn_cpw (syn_cfdif R A B)) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_pwexg (syn_cpw (syn_cfdif R A B)) (syn_cvv)
  have p0013 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cpw (syn_cfdif R A B)) (syn_cvv)) (.classMem (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A) (.classMem (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cvv)) p0008 p0013
  have p0015 :=
    @g_id (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B))))
  have p0016 :=
    @g_nceqd (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B))) p0015
  have p0017 :=
    @g_breq2d (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_cnc (.cv z)) (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) p0016
  have p0018 :=
    @g_f1eq3 (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cpw1 (syn_cpw1 A)) (.cv f)
  have p0019 :=
    @g_exbidv (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (.cv z)) (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) f dv_cache_0006 p0018
  have p0020 :=
    @g_bibi12d (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (.cv z))) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B))))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (.cv z))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))) p0017 p0019
  have p0021 :=
    @g_pw1ex A hyp_fdcolcodecardle2_2
  have p0022 :=
    @g_pw1ex (syn_cpw1 A) p0021
  have p0023 :=
    @g_vex z
  have p0024 :=
    @g_nclenc (syn_cpw1 (syn_cpw1 A)) (.cv z) f dv_cache_0007 dv_cache_0008 p0022 p0023
  have p0025 :=
    @g_vtoclg (syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (.cv z))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (.cv z)))) (syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B))))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))))) z (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cvv) dv_cache_0009 dv_cache_0010 p0020 p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (.classMem (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cvv)) (syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B))))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))))) p0014 p0025
  have p0027 :=
    @g_mpbird (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B))))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))) p0007 p0026
  exact p0027

noncomputable def g_fdcolcodetc2nc
    (A : Class) (hyp_fdcolcodetc2nc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A)))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_tcnc A hyp_fdcolcodetc2nc_1
  have p0001 :=
    @g_tceq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_pw1ex A hyp_fdcolcodetc2nc_1
  have p0004 :=
    @g_tcnc (syn_cpw1 A) p0003
  have p0005 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_cnc A))) (syn_ctc (syn_cnc (syn_cpw1 A))) (syn_cnc (syn_cpw1 (syn_cpw1 A))) p0002 p0004
  exact p0005

noncomputable def g_fdcolcodetc2le2
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdcolcodetc2le2_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcolcodetc2le2_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcolcodetc2le2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr (syn_ctc (syn_ctc (syn_cnc A))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have p0000 :=
    @g_fdcolcodetc2nc A hyp_fdcolcodetc2le2_2
  have p0001 :=
    @g_a1i (.classEq (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0000
  have p0002 :=
    @g_fdcolcodecardle2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodetc2le2_1 hyp_fdcolcodetc2le2_2 hyp_fdcolcodetc2le2_3
  have p0003 :=
    @g_eqbrtrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_clec) p0001 p0002
  exact p0003

noncomputable def g_hwcodesex
    (A : Class) (hyp_hwcodesex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_chwcodes A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0001 :=
    @g_weex
  have p0002 :=
    @g_vvex
  have p0003 :=
    @g_pwex A hyp_hwcodesex_1
  have p0004 :=
    @g_xpex (syn_cvv) (syn_cpw A) p0002 p0003
  have p0005 :=
    @g_inex (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)) p0001 p0004
  have p0006 :=
    @g_eqeltri (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cvv) p0000 p0005
  exact p0006

#print axioms g_hwcodesex

end NFChoice.DirectNominalPrf.WPPReplay
