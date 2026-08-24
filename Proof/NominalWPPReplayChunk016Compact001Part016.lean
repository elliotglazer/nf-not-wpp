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
import NominalWPPReplayChunk016Compact001Part015

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

noncomputable def g_weincsegcutorwholendv
    (x : Var) (y : Var) (D : Class) (R : Class) (dv_D_y : y ∉ D.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) (hyp_weincsegcutorwholendv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv x) D) (syn_wo (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (syn_wrex y D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, dv_R_y, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0009 : y ∉ ((syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_D_y, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_orc (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (syn_wrex y D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0001 :=
    @g_a1i (.imp (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (syn_wo (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (syn_wrex y D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) (.classMem (.cv x) D) p0000
  have p0002 :=
    @g_simpl (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))
  have p0003 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0004 :=
    @g_a1i (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D) (.classMem (.cv x) D) p0003
  have p0005 :=
    @g_snssi (.cv x) D
  have p0006 :=
    @g_jca (.classMem (.cv x) D) (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D) (syn_wss (syn_csn (.cv x)) D) p0004 p0005
  have p0007 :=
    @g_unss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)) D
  have p0008 :=
    @g_sylib (.classMem (.cv x) D) (syn_wa (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D) (syn_wss (syn_csn (.cv x)) D)) (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) p0006 p0007
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv x) D) (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) p0002 p0008
  have p0010 :=
    @g_simpr (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))
  have p0011 :=
    @g_jca (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D)) p0009 p0010
  have p0012 :=
    @g_dfpss2 (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D
  have p0013 :=
    @g_sylibr (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wa (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wpss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) p0011 p0012
  have p0014 :=
    @g_dfpss3 (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D
  have p0015 :=
    @g_sylib (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wpss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (syn_wa (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (.neg (syn_wss D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) p0013 p0014
  have p0016 :=
    @g_simpr (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (.neg (syn_wss D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0017 :=
    @g_syl (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wa (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (.neg (syn_wss D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.neg (syn_wss D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) p0015 p0016
  have p0018 :=
    @g_nss z D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) dv_cache_0001 dv_cache_0002
  have p0019 :=
    @g_sylib (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.neg (syn_wss D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wex z (syn_wa (.classMem (.cv z) D) (.neg (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))))) p0017 p0018
  have p0020 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex z D (.neg (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))))))
  have p0021 :=
    @g_sylibr (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wex z (syn_wa (.classMem (.cv z) D) (.neg (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))))) (syn_wrex z D (.neg (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) p0019 p0020
  have p0022 :=
    @g_brex R D (syn_cwe)
  have p0023 :=
    Nominal.mp hyp_weincsegcutorwholendv_1 p0022
  have p0024 :=
    @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_brex R D (syn_cwe)
  have p0027 :=
    Nominal.mp hyp_weincsegcutorwholendv_1 p0026
  have p0028 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_idex
  have p0031 :=
    @g_difex R (syn_cid) p0029 p0030
  have p0032 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0031
  have p0033 :=
    @g_snex (.cv x)
  have p0034 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0032 p0033
  have p0035 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0025 p0034
  have p0036 :=
    @g_snex (.cv x)
  have p0037 :=
    @g_unex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)) p0035 p0036
  have p0038 :=
    @g_wedifleastssndv z y (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D R dv_cache_0002 dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_weincsegcutorwholendv_1 p0037
  have p0039 :=
    @g_syl (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wrex z D (.neg (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) p0021 p0038
  have p0040 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
  have p0041 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0040 p0041
  have p0043 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
  have p0044 :=
    @g_simpl (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) p0043 p0044
  have p0046 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (.classMem (.cv y) D) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) p0042 p0045
  have p0047 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
  have p0048 :=
    @g_simpr (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))
  have p0049 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))) p0047 p0048
  have p0050 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv y) D) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))) p0046 p0049
  have p0051 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
  have p0052 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) p0051 p0052
  have p0054 :=
    @g_simpl (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))
  have p0055 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv x) D) p0053 p0054
  have p0056 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
  have p0057 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)
  have p0058 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0056 p0057
  have p0059 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (.classMem (.cv x) D) (.classMem (.cv y) D) p0055 p0058
  have p0060 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
  have p0061 :=
    @g_simpl (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))
  have p0062 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) p0060 p0061
  have p0063 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) p0059 p0062
  have p0064 :=
    @g_weincsegsscutndv x y D R dv_cache_0008 hyp_weincsegcutorwholendv_1
  have p0065 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0063 p0064
  have p0066 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (syn_wa (.classMem (.cv y) D) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))) (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0050 p0065
  have p0067 :=
    @g_wedownexactcutndv y (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D R hyp_weincsegcutorwholendv_1
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))) (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0066 p0067
  have p0069 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0068
  have p0070 :=
    @g_reximdva (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) y D dv_cache_0009 p0069
  have p0071 :=
    @g_mpd (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wrex y D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0039 p0070
  have p0072 :=
    @g_olcd (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D))) (syn_wrex y D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) p0071
  have p0073 :=
    @g_ex (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D)) (syn_wo (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (syn_wrex y D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) p0072
  have p0074 :=
    @g_pm2_61d (.classMem (.cv x) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (syn_wo (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) D) (syn_wrex y D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) p0001 p0073
  exact p0074

noncomputable def g_elwecutisoclterminalndv
    (x : Var) (u : Var) (D : Class) (R : Class) (S : Class) (E : Class) (K : Class) (dv_D_u : u ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_K_u : u ∉ K.fv) (dv_K_x : x ∉ K.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_u : u ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_u_x : u ≠ x) :
    Nominal.NPrf (.imp (.classMem K (syn_cvv)) (syn_wb (.classMem K (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E (syn_wiso K (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ K.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_x : h ≠ x := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_h : x ≠ h :=
    Ne.symm fresh_h_ne_x
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_h : u ≠ h :=
    Ne.symm fresh_h_ne_u
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_h_not_R : h ∉ R.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_h_not_S : h ∉ S.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_E : h ∉ E.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_K : h ∉ K.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((Wff.classEq (.cv h) K)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_h, dv_K_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv h) K)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_h, dv_K_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0012 : h ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have dv_cache_0013 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0014 : h ∉ (K).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : h ∉ ((syn_wb (.classMem K (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E (syn_wiso K (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_K, fresh_h_not_D, fresh_h_not_E, fresh_h_not_R, fresh_h_not_S, fresh_h_ne_x, fresh_h_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv h) K)
  have p0001 :=
    @g_eleq1d (.classEq (.cv h) K) (.cv h) K (syn_cwecutiso R D S E) p0000
  have p0002 :=
    @g_isoeq1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) K (.cv h)
  have p0003 :=
    @g_rexbidv (.classEq (.cv h) K) (syn_wiso (.cv h) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wiso K (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) u E dv_cache_0001 p0002
  have p0004 :=
    @g_rexbidv (.classEq (.cv h) K) (syn_wrex u E (syn_wiso (.cv h) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wrex u E (syn_wiso K (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) x D dv_cache_0002 p0003
  have p0005 :=
    @g_bibi12d (.classEq (.cv h) K) (.classMem (.cv h) (syn_cwecutiso R D S E)) (.classMem K (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E (syn_wiso (.cv h) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) (syn_wrex x D (syn_wrex u E (syn_wiso K (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) p0001 p0004
  have p0006 :=
    @g_elwecutiso x u D R S h E dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0007 :=
    @g_vtoclg (syn_wb (.classMem (.cv h) (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E (syn_wiso (.cv h) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))) (syn_wb (.classMem K (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E (syn_wiso K (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))) h K (syn_cvv) dv_cache_0014 dv_cache_0015 p0005 p0006
  exact p0007

#print axioms g_elwecutisoclterminalndv

end NFChoice.DirectNominalPrf.WPPReplay
