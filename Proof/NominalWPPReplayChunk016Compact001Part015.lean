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
import NominalWPPReplayChunk016Compact001Part014

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

noncomputable def g_wedownexactcutndv
    (x : Var) (C : Class) (D : Class) (R : Class) (hyp_wedownexactcutndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classEq C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, fresh_y_not_C, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0001 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0000 p0001
  have p0003 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0004 :=
    @g_elstrictseg x y D R
  have p0005 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0003 p0004
  have p0006 :=
    @g_simprr (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) (syn_wne (.cv y) (.cv x)) p0005 p0006
  have p0008 :=
    @g_wppweantisym D R
  have p0009 :=
    Nominal.mp hyp_wedownexactcutndv_1 p0008
  have p0010 :=
    @g_a1i (syn_wbr R (syn_cantisym) D) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) p0009
  have p0011 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))
  have p0012 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0013 :=
    @g_elstrictseg x y D R
  have p0014 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0012 p0013
  have p0015 :=
    @g_simpl (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) (.classMem (.cv y) D) p0014 p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) D) p0011 p0016
  have p0018 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))
  have p0019 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) p0019 p0020
  have p0022 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) p0021 p0022
  have p0024 :=
    @g_simpl (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (.classMem (.cv x) D) p0023 p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv x) D) p0018 p0025
  have p0027 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))
  have p0028 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0029 :=
    @g_elstrictseg x y D R
  have p0030 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0028 p0029
  have p0031 :=
    @g_simprl (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) (syn_wbr (.cv y) R (.cv x)) p0030 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv y) R (.cv x)) p0027 p0032
  have p0034 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))
  have p0035 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0036 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) p0035 p0036
  have p0038 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))
  have p0039 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x)))) p0037 p0038
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x)))) p0034 p0039
  have p0041 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))
  have p0042 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0043 :=
    @g_elstrictseg x y D R
  have p0044 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0042 p0043
  have p0045 :=
    @g_simpl (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) (.classMem (.cv y) D) p0044 p0045
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) D) p0041 p0046
  have p0048 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))
  have p0049 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) (.classMem (.cv y) D) (.neg (.classMem (.cv y) C)) p0047 p0048
  have p0050 :=
    @g_eldif (.cv y) D C
  have p0051 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) (syn_wa (.classMem (.cv y) D) (.neg (.classMem (.cv y) C))) (.classMem (.cv y) (syn_cdif D C)) p0049 p0050
  have p0052 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) (syn_cdif D C) (syn_cima R (syn_csn (.cv x))) (.cv y) p0040 p0051
  have p0053 :=
    @g_elimasn R (.cv x) (.cv y)
  have p0054 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) R (.cv y))))
  have p0055 :=
    @g_bitr4i (.classMem (.cv y) (syn_cima R (syn_csn (.cv x)))) (.classMem (syn_cop (.cv x) (.cv y)) R) (syn_wbr (.cv x) R (.cv y)) p0053 p0054
  have p0056 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) (.classMem (.cv y) (syn_cima R (syn_csn (.cv x)))) (syn_wbr (.cv x) R (.cv y)) p0052 p0055
  have p0057 :=
    @g_antid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C))) D R (.cv y) (.cv x) p0010 p0017 p0026 p0033 p0056
  have p0058 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C)) (.classEq (.cv y) (.cv x)) p0057
  have p0059 :=
    @g_necon3ad (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classMem (.cv y) C)) (.cv y) (.cv x) p0058
  have p0060 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wne (.cv y) (.cv x)) (.neg (.neg (.classMem (.cv y) C))) p0007 p0059
  have p0061 :=
    @g_notnotrd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) C) p0060
  have p0062 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) C) p0061
  have p0063 :=
    @g_ssrdv (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) y (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) C dv_cache_0001 dv_cache_0002 dv_cache_0003 p0062
  have p0064 :=
    @g_eqssd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv x))))) (syn_wss C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) C (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0002 p0063
  exact p0064

#print axioms g_wedownexactcutndv

end NFChoice.DirectNominalPrf.WPPReplay
