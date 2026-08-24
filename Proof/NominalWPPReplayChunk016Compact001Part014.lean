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
import NominalWPPReplayChunk016Compact001Part013

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

noncomputable def g_weincsegsscutndv
    (x : Var) (y : Var) (D : Class) (R : Class) (dv_x_y : x ≠ y) (hyp_weincsegsscutndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wss (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) := by
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
  have dv_cache_0001 : z ∉ ((syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_D, fresh_z_ne_y, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0001 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0002 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0003 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0004 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0002 p0003
  have p0005 :=
    @g_strictsegdifinindv x D R
  have p0006 :=
    @g_uneq1i (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x)) p0005
  have p0007 :=
    @g_a1i (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x)))) (.classMem (.cv x) D) p0006
  have p0008 :=
    @g_id (.classMem (.cv x) D)
  have p0009 :=
    @g_wppweref D R
  have p0010 :=
    Nominal.mp hyp_weincsegsscutndv_1 p0009
  have p0011 :=
    @g_a1i (syn_wbr R (syn_cref) D) (.classMem (.cv x) D) p0010
  have p0012 :=
    @g_id (.classMem (.cv x) D)
  have p0013 :=
    @g_refd (.classMem (.cv x) D) D R (.cv x) p0011 p0012
  have p0014 :=
    @g_eliniseg R (.cv x) (.cv x)
  have p0015 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wbr (.cv x) R (.cv x)) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0013 p0014
  have p0016 :=
    @g_jca (.classMem (.cv x) D) (.classMem (.cv x) D) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0008 p0015
  have p0017 :=
    @g_elin (.cv x) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0018 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wa (.classMem (.cv x) D) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0016 p0017
  have p0019 :=
    @g_nnsucelrlem4 (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0020 :=
    @g_syl (.classMem (.cv x) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classEq (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0018 p0019
  have p0021 :=
    @g_eqtrd (.classMem (.cv x) D) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0007 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv x) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0004 p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0001 p0022
  have p0024 :=
    @g_eleqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0000 p0023
  have p0025 :=
    @g_elin (.cv z) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0026 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0024 p0025
  have p0027 :=
    @g_simpl (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classMem (.cv z) D) p0026 p0027
  have p0029 :=
    @g_wppwepo D R
  have p0030 :=
    Nominal.mp hyp_weincsegsscutndv_1 p0029
  have p0031 :=
    @g_porta D R
  have p0032 :=
    @g_simp2bi (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0031
  have p0033 :=
    Nominal.mp p0030 p0032
  have p0034 :=
    @g_a1i (syn_wbr R (syn_ctrans) D) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) p0033
  have p0035 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0036 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0037 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0038 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0039 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0037 p0038
  have p0040 :=
    @g_strictsegdifinindv x D R
  have p0041 :=
    @g_uneq1i (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x)) p0040
  have p0042 :=
    @g_a1i (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x)))) (.classMem (.cv x) D) p0041
  have p0043 :=
    @g_id (.classMem (.cv x) D)
  have p0044 :=
    @g_wppweref D R
  have p0045 :=
    Nominal.mp hyp_weincsegsscutndv_1 p0044
  have p0046 :=
    @g_a1i (syn_wbr R (syn_cref) D) (.classMem (.cv x) D) p0045
  have p0047 :=
    @g_id (.classMem (.cv x) D)
  have p0048 :=
    @g_refd (.classMem (.cv x) D) D R (.cv x) p0046 p0047
  have p0049 :=
    @g_eliniseg R (.cv x) (.cv x)
  have p0050 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wbr (.cv x) R (.cv x)) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0048 p0049
  have p0051 :=
    @g_jca (.classMem (.cv x) D) (.classMem (.cv x) D) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0043 p0050
  have p0052 :=
    @g_elin (.cv x) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0053 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wa (.classMem (.cv x) D) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0051 p0052
  have p0054 :=
    @g_nnsucelrlem4 (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0055 :=
    @g_syl (.classMem (.cv x) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classEq (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0053 p0054
  have p0056 :=
    @g_eqtrd (.classMem (.cv x) D) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0042 p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv x) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0039 p0056
  have p0058 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0036 p0057
  have p0059 :=
    @g_eleqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0035 p0058
  have p0060 :=
    @g_elin (.cv z) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0061 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0059 p0060
  have p0062 :=
    @g_simpl (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classMem (.cv z) D) p0061 p0062
  have p0064 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0065 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0066 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0067 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0065 p0066
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv x) D) p0064 p0067
  have p0069 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0070 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0071 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0072 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0070 p0071
  have p0073 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv y) D) p0069 p0072
  have p0074 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0075 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0076 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0077 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0078 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0076 p0077
  have p0079 :=
    @g_strictsegdifinindv x D R
  have p0080 :=
    @g_uneq1i (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x)) p0079
  have p0081 :=
    @g_a1i (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x)))) (.classMem (.cv x) D) p0080
  have p0082 :=
    @g_id (.classMem (.cv x) D)
  have p0083 :=
    @g_wppweref D R
  have p0084 :=
    Nominal.mp hyp_weincsegsscutndv_1 p0083
  have p0085 :=
    @g_a1i (syn_wbr R (syn_cref) D) (.classMem (.cv x) D) p0084
  have p0086 :=
    @g_id (.classMem (.cv x) D)
  have p0087 :=
    @g_refd (.classMem (.cv x) D) D R (.cv x) p0085 p0086
  have p0088 :=
    @g_eliniseg R (.cv x) (.cv x)
  have p0089 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wbr (.cv x) R (.cv x)) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0087 p0088
  have p0090 :=
    @g_jca (.classMem (.cv x) D) (.classMem (.cv x) D) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0082 p0089
  have p0091 :=
    @g_elin (.cv x) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0092 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wa (.classMem (.cv x) D) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0090 p0091
  have p0093 :=
    @g_nnsucelrlem4 (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0094 :=
    @g_syl (.classMem (.cv x) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classEq (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0092 p0093
  have p0095 :=
    @g_eqtrd (.classMem (.cv x) D) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0081 p0094
  have p0096 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv x) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0078 p0095
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0075 p0096
  have p0098 :=
    @g_eleqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0074 p0097
  have p0099 :=
    @g_elin (.cv z) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0100 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0098 p0099
  have p0101 :=
    @g_simpr (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0102 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0100 p0101
  have p0103 :=
    @g_eliniseg R (.cv x) (.cv z)
  have p0104 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (.classMem (.cv z) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_wbr (.cv z) R (.cv x)) p0102 p0103
  have p0105 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0106 :=
    @g_wppweconnex D R
  have p0107 :=
    Nominal.mp hyp_weincsegsscutndv_1 p0106
  have p0108 :=
    @g_a1i (syn_wbr R (syn_cconnex) D) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) p0107
  have p0109 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0110 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0111 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0109 p0110
  have p0112 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0113 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0114 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0112 p0113
  have p0115 :=
    @g_connexd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) D R (.cv x) (.cv y) p0108 p0111 p0114
  have p0116 :=
    @g_id (syn_wbr (.cv x) R (.cv y))
  have p0117 :=
    @g_a1i (.imp (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) p0116
  have p0118 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0119 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0120 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0121 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0119 p0120
  have p0122 :=
    @g_strictsegdifinindv x D R
  have p0123 :=
    @g_uneq1i (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x)) p0122
  have p0124 :=
    @g_a1i (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x)))) (.classMem (.cv x) D) p0123
  have p0125 :=
    @g_id (.classMem (.cv x) D)
  have p0126 :=
    @g_wppweref D R
  have p0127 :=
    Nominal.mp hyp_weincsegsscutndv_1 p0126
  have p0128 :=
    @g_a1i (syn_wbr R (syn_cref) D) (.classMem (.cv x) D) p0127
  have p0129 :=
    @g_id (.classMem (.cv x) D)
  have p0130 :=
    @g_refd (.classMem (.cv x) D) D R (.cv x) p0128 p0129
  have p0131 :=
    @g_eliniseg R (.cv x) (.cv x)
  have p0132 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wbr (.cv x) R (.cv x)) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0130 p0131
  have p0133 :=
    @g_jca (.classMem (.cv x) D) (.classMem (.cv x) D) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0125 p0132
  have p0134 :=
    @g_elin (.cv x) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0135 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wa (.classMem (.cv x) D) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0133 p0134
  have p0136 :=
    @g_nnsucelrlem4 (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))
  have p0137 :=
    @g_syl (.classMem (.cv x) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classEq (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0135 p0136
  have p0138 :=
    @g_eqtrd (.classMem (.cv x) D) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0124 p0137
  have p0139 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv x) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0121 p0138
  have p0140 :=
    @g_neleqtrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (.cv y) p0118 p0139
  have p0141 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x))
  have p0142 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0143 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0144 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0142 p0143
  have p0145 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv y) D) p0141 p0144
  have p0146 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x))
  have p0147 :=
    @g_eliniseg R (.cv x) (.cv y)
  have p0148 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv y) R (.cv x)) (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0146 p0147
  have p0149 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x))) (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) p0145 p0148
  have p0150 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0151 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x))) (syn_wa (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0149 p0150
  have p0152 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x)) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0151
  have p0153 :=
    @g_con3d (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x)) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) p0152
  have p0154 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))))) (.neg (syn_wbr (.cv y) R (.cv x))) p0140 p0153
  have p0155 :=
    @g_pm2_21d (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv x) R (.cv y)) p0154
  have p0156 :=
    @g_jaod (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)) p0117 p0155
  have p0157 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv x) R (.cv y)) p0115 p0156
  have p0158 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (.cv y)) p0105 p0157
  have p0159 :=
    @g_trd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) D R (.cv z) (.cv x) (.cv y) p0034 p0063 p0068 p0073 p0104 p0158
  have p0160 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0161 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))
  have p0162 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))
  have p0163 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) p0161 p0162
  have p0164 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) p0160 p0163
  have p0165 :=
    @g_nelne2 (.cv z) (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))
  have p0166 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (syn_wne (.cv z) (.cv y)) p0164 p0165
  have p0167 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wbr (.cv z) R (.cv y)) (syn_wne (.cv z) (.cv y)) p0159 p0166
  have p0168 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv y)) (syn_wne (.cv z) (.cv y))) p0028 p0167
  have p0169 :=
    @g_elstrictseg y z D R
  have p0170 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv y)) (syn_wne (.cv z) (.cv y)))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0168 p0169
  have p0171 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0170
  have p0172 :=
    @g_ssrdv (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x)))))) z (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0171
  exact p0172

#print axioms g_weincsegsscutndv

end NFChoice.DirectNominalPrf.WPPReplay
