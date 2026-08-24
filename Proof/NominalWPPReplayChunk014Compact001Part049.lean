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
import NominalWPPReplayChunk014Compact001Part048

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

noncomputable def g_strictseghwnisono
    (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) := by
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
  have dv_cache_0002 : z ∉ ((syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0001 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0002 :=
    @g_brex (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_chwniso D)
  have p0003 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv))) p0001 p0002
  have p0004 :=
    @g_hwnisohwisocl D (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0005 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv))) (.imp (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwiso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) p0003 p0004
  have p0006 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwiso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0000 p0005
  have p0007 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0008 :=
    @g_brex (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_chwniso D)
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv))) p0007 p0008
  have p0010 :=
    @g_hwisowitnesscl D (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) z dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv))) (.imp (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwiso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wex z (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))))) p0009 p0010
  have p0012 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwiso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wex z (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) p0006 p0011
  have p0013 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0014 :=
    @g_nfv (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) z dv_cache_0004
  have p0015 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0016 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0017 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0015 p0016
  have p0018 :=
    @g_brex R D (syn_cwe)
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0017 p0018
  have p0020 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0019
  have p0021 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0022 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0021 p0022
  have p0024 :=
    @g_brex R D (syn_cwe)
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0023 p0024
  have p0026 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0025
  have p0027 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0028 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0027 p0028
  have p0030 :=
    @g_brex R D (syn_cwe)
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0029 p0030
  have p0032 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0031
  have p0033 :=
    @g_idex
  have p0034 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0033
  have p0035 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0032 p0034
  have p0036 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0035 p0036
  have p0038 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0039 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0037 p0038
  have p0040 :=
    @g_snex (.cv x)
  have p0041 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0040
  have p0042 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0039 p0041
  have p0043 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0042 p0043
  have p0045 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0026 p0044
  have p0046 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv) (syn_cvv)
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0045 p0046
  have p0048 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0049 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0050 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0048 p0049
  have p0051 :=
    @g_brex R D (syn_cwe)
  have p0052 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0050 p0051
  have p0053 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0052
  have p0054 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0055 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0056 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0054 p0055
  have p0057 :=
    @g_brex R D (syn_cwe)
  have p0058 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0056 p0057
  have p0059 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0058
  have p0060 :=
    @g_idex
  have p0061 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0060
  have p0062 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0059 p0061
  have p0063 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0062 p0063
  have p0065 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0066 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0064 p0065
  have p0067 :=
    @g_snex (.cv x)
  have p0068 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0067
  have p0069 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0066 p0068
  have p0070 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0069 p0070
  have p0072 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0053 p0071
  have p0073 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv) (syn_cvv)
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0072 p0073
  have p0075 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0047 p0074
  have p0076 :=
    @g_xpexg (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv) (syn_cvv)
  have p0077 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv))) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) p0075 p0076
  have p0078 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) p0020 p0077
  have p0079 :=
    @g_inexg R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv) (syn_cvv)
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv))) (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) p0078 p0079
  have p0081 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0082 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0083 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0081 p0082
  have p0084 :=
    @g_brex R D (syn_cwe)
  have p0085 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0083 p0084
  have p0086 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0085
  have p0087 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0088 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0089 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0087 p0088
  have p0090 :=
    @g_brex R D (syn_cwe)
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0089 p0090
  have p0092 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0091
  have p0093 :=
    @g_idex
  have p0094 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0093
  have p0095 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0092 p0094
  have p0096 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0095 p0096
  have p0098 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0099 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0097 p0098
  have p0100 :=
    @g_snex (.cv x)
  have p0101 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0100
  have p0102 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0099 p0101
  have p0103 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0104 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0102 p0103
  have p0105 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0086 p0104
  have p0106 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv) (syn_cvv)
  have p0107 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0105 p0106
  have p0108 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0080 p0107
  have p0109 :=
    @g_opfvscl (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0110 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0108 p0109
  have p0111 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0110
  have p0112 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.cv z)
  have p0113 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wb (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) p0111 p0112
  have p0114 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0115 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0116 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0114 p0115
  have p0117 :=
    @g_brex R D (syn_cwe)
  have p0118 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0116 p0117
  have p0119 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0118
  have p0120 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0121 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0122 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0120 p0121
  have p0123 :=
    @g_brex R D (syn_cwe)
  have p0124 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0122 p0123
  have p0125 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0124
  have p0126 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0127 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0128 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0126 p0127
  have p0129 :=
    @g_brex R D (syn_cwe)
  have p0130 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0128 p0129
  have p0131 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0130
  have p0132 :=
    @g_idex
  have p0133 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0132
  have p0134 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0131 p0133
  have p0135 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0136 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0134 p0135
  have p0137 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0138 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0136 p0137
  have p0139 :=
    @g_snex (.cv y)
  have p0140 :=
    @g_a1i (.classMem (syn_csn (.cv y)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0139
  have p0141 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv)) p0138 p0140
  have p0142 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)) (syn_cvv) (syn_cvv)
  have p0143 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0141 p0142
  have p0144 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0125 p0143
  have p0145 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv) (syn_cvv)
  have p0146 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0144 p0145
  have p0147 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0148 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0149 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0147 p0148
  have p0150 :=
    @g_brex R D (syn_cwe)
  have p0151 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0149 p0150
  have p0152 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0151
  have p0153 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0154 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0155 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0153 p0154
  have p0156 :=
    @g_brex R D (syn_cwe)
  have p0157 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0155 p0156
  have p0158 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0157
  have p0159 :=
    @g_idex
  have p0160 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0159
  have p0161 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0158 p0160
  have p0162 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0163 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0161 p0162
  have p0164 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0165 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0163 p0164
  have p0166 :=
    @g_snex (.cv y)
  have p0167 :=
    @g_a1i (.classMem (syn_csn (.cv y)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0166
  have p0168 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv)) p0165 p0167
  have p0169 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)) (syn_cvv) (syn_cvv)
  have p0170 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0168 p0169
  have p0171 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0152 p0170
  have p0172 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv) (syn_cvv)
  have p0173 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0171 p0172
  have p0174 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0146 p0173
  have p0175 :=
    @g_xpexg (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv) (syn_cvv)
  have p0176 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv))) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv)) p0174 p0175
  have p0177 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv)) p0119 p0176
  have p0178 :=
    @g_inexg R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv) (syn_cvv)
  have p0179 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv))) (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cvv)) p0177 p0178
  have p0180 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0181 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0182 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0180 p0181
  have p0183 :=
    @g_brex R D (syn_cwe)
  have p0184 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0182 p0183
  have p0185 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0184
  have p0186 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0187 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0188 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0186 p0187
  have p0189 :=
    @g_brex R D (syn_cwe)
  have p0190 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0188 p0189
  have p0191 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0190
  have p0192 :=
    @g_idex
  have p0193 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0192
  have p0194 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0191 p0193
  have p0195 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0196 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0194 p0195
  have p0197 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0198 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0196 p0197
  have p0199 :=
    @g_snex (.cv y)
  have p0200 :=
    @g_a1i (.classMem (syn_csn (.cv y)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0199
  have p0201 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv)) p0198 p0200
  have p0202 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)) (syn_cvv) (syn_cvv)
  have p0203 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0201 p0202
  have p0204 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0185 p0203
  have p0205 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv) (syn_cvv)
  have p0206 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0204 p0205
  have p0207 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0179 p0206
  have p0208 :=
    @g_opfvscl (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
  have p0209 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0207 p0208
  have p0210 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0209
  have p0211 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.cv z)
  have p0212 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wb (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) p0210 p0211
  have p0213 :=
    @g_bitrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) p0113 p0212
  have p0214 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0215 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0216 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0214 p0215
  have p0217 :=
    @g_brex R D (syn_cwe)
  have p0218 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0216 p0217
  have p0219 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0218
  have p0220 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0221 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0222 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0220 p0221
  have p0223 :=
    @g_brex R D (syn_cwe)
  have p0224 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0222 p0223
  have p0225 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0224
  have p0226 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0227 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0228 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0226 p0227
  have p0229 :=
    @g_brex R D (syn_cwe)
  have p0230 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0228 p0229
  have p0231 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0230
  have p0232 :=
    @g_idex
  have p0233 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0232
  have p0234 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0231 p0233
  have p0235 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0236 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0234 p0235
  have p0237 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0238 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0236 p0237
  have p0239 :=
    @g_snex (.cv x)
  have p0240 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0239
  have p0241 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0238 p0240
  have p0242 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0243 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0241 p0242
  have p0244 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0225 p0243
  have p0245 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv) (syn_cvv)
  have p0246 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0244 p0245
  have p0247 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0248 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0249 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0247 p0248
  have p0250 :=
    @g_brex R D (syn_cwe)
  have p0251 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0249 p0250
  have p0252 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0251
  have p0253 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0254 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0255 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0253 p0254
  have p0256 :=
    @g_brex R D (syn_cwe)
  have p0257 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0255 p0256
  have p0258 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0257
  have p0259 :=
    @g_idex
  have p0260 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0259
  have p0261 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0258 p0260
  have p0262 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0263 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0261 p0262
  have p0264 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0265 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0263 p0264
  have p0266 :=
    @g_snex (.cv x)
  have p0267 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0266
  have p0268 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0265 p0267
  have p0269 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0270 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0268 p0269
  have p0271 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0252 p0270
  have p0272 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv) (syn_cvv)
  have p0273 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0271 p0272
  have p0274 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0246 p0273
  have p0275 :=
    @g_xpexg (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv) (syn_cvv)
  have p0276 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv))) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) p0274 p0275
  have p0277 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) p0219 p0276
  have p0278 :=
    @g_inexg R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv) (syn_cvv)
  have p0279 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv))) (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) p0277 p0278
  have p0280 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0281 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0282 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0280 p0281
  have p0283 :=
    @g_brex R D (syn_cwe)
  have p0284 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0282 p0283
  have p0285 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0284
  have p0286 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0287 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0288 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0286 p0287
  have p0289 :=
    @g_brex R D (syn_cwe)
  have p0290 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0288 p0289
  have p0291 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0290
  have p0292 :=
    @g_idex
  have p0293 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0292
  have p0294 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0291 p0293
  have p0295 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0296 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0294 p0295
  have p0297 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0298 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0296 p0297
  have p0299 :=
    @g_snex (.cv x)
  have p0300 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0299
  have p0301 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0298 p0300
  have p0302 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0303 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0301 p0302
  have p0304 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0285 p0303
  have p0305 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv) (syn_cvv)
  have p0306 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0304 p0305
  have p0307 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0279 p0306
  have p0308 :=
    @g_opfvscl (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0309 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0307 p0308
  have p0310 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0309
  have p0311 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.cv z)
  have p0312 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wb (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) p0310 p0311
  have p0313 :=
    @g_bitrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) p0213 p0312
  have p0314 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0315 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0316 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0314 p0315
  have p0317 :=
    @g_brex R D (syn_cwe)
  have p0318 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0316 p0317
  have p0319 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0318
  have p0320 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0321 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0322 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0320 p0321
  have p0323 :=
    @g_brex R D (syn_cwe)
  have p0324 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0322 p0323
  have p0325 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0324
  have p0326 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0327 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0328 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0326 p0327
  have p0329 :=
    @g_brex R D (syn_cwe)
  have p0330 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0328 p0329
  have p0331 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0330
  have p0332 :=
    @g_idex
  have p0333 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0332
  have p0334 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0331 p0333
  have p0335 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0336 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0334 p0335
  have p0337 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0338 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0336 p0337
  have p0339 :=
    @g_snex (.cv y)
  have p0340 :=
    @g_a1i (.classMem (syn_csn (.cv y)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0339
  have p0341 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv)) p0338 p0340
  have p0342 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)) (syn_cvv) (syn_cvv)
  have p0343 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0341 p0342
  have p0344 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0325 p0343
  have p0345 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv) (syn_cvv)
  have p0346 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0344 p0345
  have p0347 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0348 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0349 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0347 p0348
  have p0350 :=
    @g_brex R D (syn_cwe)
  have p0351 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0349 p0350
  have p0352 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0351
  have p0353 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0354 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0355 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0353 p0354
  have p0356 :=
    @g_brex R D (syn_cwe)
  have p0357 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0355 p0356
  have p0358 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0357
  have p0359 :=
    @g_idex
  have p0360 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0359
  have p0361 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0358 p0360
  have p0362 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0363 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0361 p0362
  have p0364 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0365 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0363 p0364
  have p0366 :=
    @g_snex (.cv y)
  have p0367 :=
    @g_a1i (.classMem (syn_csn (.cv y)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0366
  have p0368 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv)) p0365 p0367
  have p0369 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)) (syn_cvv) (syn_cvv)
  have p0370 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0368 p0369
  have p0371 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0352 p0370
  have p0372 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv) (syn_cvv)
  have p0373 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0371 p0372
  have p0374 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0346 p0373
  have p0375 :=
    @g_xpexg (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv) (syn_cvv)
  have p0376 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv))) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv)) p0374 p0375
  have p0377 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv)) p0319 p0376
  have p0378 :=
    @g_inexg R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv) (syn_cvv)
  have p0379 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv))) (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cvv)) p0377 p0378
  have p0380 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0381 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0382 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0380 p0381
  have p0383 :=
    @g_brex R D (syn_cwe)
  have p0384 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0382 p0383
  have p0385 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0384
  have p0386 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0387 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0388 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0386 p0387
  have p0389 :=
    @g_brex R D (syn_cwe)
  have p0390 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0388 p0389
  have p0391 :=
    @g_simpld (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0390
  have p0392 :=
    @g_idex
  have p0393 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0392
  have p0394 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0391 p0393
  have p0395 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0396 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0394 p0395
  have p0397 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0398 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0396 p0397
  have p0399 :=
    @g_snex (.cv y)
  have p0400 :=
    @g_a1i (.classMem (syn_csn (.cv y)) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0399
  have p0401 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv)) p0398 p0400
  have p0402 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)) (syn_cvv) (syn_cvv)
  have p0403 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0401 p0402
  have p0404 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)) p0385 p0403
  have p0405 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv) (syn_cvv)
  have p0406 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0404 p0405
  have p0407 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)) p0379 p0406
  have p0408 :=
    @g_opfvscl (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
  have p0409 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0407 p0408
  have p0410 :=
    @g_simprd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0409
  have p0411 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.cv z)
  have p0412 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wb (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0410 p0411
  have p0413 :=
    @g_bitrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0313 p0412
  have p0414 :=
    @g_biimpd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0413
  have p0415 :=
    @g_eximd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) z p0014 p0414
  have p0416 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.imp (syn_wex z (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) (syn_wex z (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) p0013 p0415
  have p0417 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wex z (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) (syn_wex z (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0012 p0416
  have p0418 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0419 :=
    @g_id (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0420 :=
    @g_vex z
  have p0421 :=
    @g_a1i (.classMem (.cv z) (syn_cvv)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0420
  have p0422 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv z) (syn_cvv)) p0419 p0421
  have p0423 :=
    @g_strictsegltnoiso x y D R (.cv z)
  have p0424 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv z) (syn_cvv))) (.neg (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0422 p0423
  have p0425 :=
    @g_nexdv (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) z dv_cache_0004 p0424
  have p0426 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (syn_wex z (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) p0418 p0425
  have p0427 :=
    @g_pm2_21dd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wex z (syn_wiso (.cv z) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) p0417 p0426
  have p0428 :=
    @g_pm2_01da (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0427
  exact p0428

#print axioms g_strictseghwnisono

end NFChoice.DirectNominalPrf.WPPReplay
