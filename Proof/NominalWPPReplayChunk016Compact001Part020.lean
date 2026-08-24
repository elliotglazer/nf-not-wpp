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
import NominalWPPReplayChunk016Compact001Part019

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

noncomputable def g_wecutisogenfixedrev
    (x : Var) (y : Var) (D : Class) (R : Class) (S : Class) (f : Var) (E : Class) (r : Var) (dv_D_f : f ∉ D.fv) (dv_D_r : r ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_r : r ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_E_y : y ∉ E.fv) (dv_R_f : f ∉ R.fv) (dv_R_r : r ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_f : f ∉ S.fv) (dv_S_r : r ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_f_r : f ≠ r) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y) (dv_r_x : r ≠ x) (dv_r_y : r ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classMem (.cv f) (syn_cwecutiso R D S E))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({f} : Finset Var) ∪ E.fv ∪ ({r} : Finset Var)
  have dv_cache_0001 : y ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : f ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ y from (by exact dv_f_y))
  have dv_cache_0010 : f ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact dv_f_x))
  have dv_cache_0011 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))
  have p0001 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))
  have p0004 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0003 p0004
  have p0006 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))
  have p0007 :=
    @g_simpl (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0008 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0006 p0007
  have p0009 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))
  have p0010 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0011 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) p0009 p0010
  have p0012 :=
    @g_simpl (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) p0011 p0012
  have p0014 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x))))
  have p0015 :=
    @g_a1i (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) p0014
  have p0016 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0013 p0015
  have p0017 :=
    @g_opth (.cv r) (syn_cdm (.cv f)) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0018 :=
    @g_sylib (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classEq (.cv r) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0016 p0017
  have p0019 :=
    @g_simpl (.classEq (.cv r) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classEq (.cv r) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classEq (.cv r) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0018 p0019
  have p0021 :=
    @g_isoeq2 (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.cv f)
  have p0022 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classEq (.cv r) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wb (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f)))) p0020 p0021
  have p0023 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))
  have p0024 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) p0023 p0024
  have p0026 :=
    @g_simpr (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0027 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))) p0025 p0026
  have p0028 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode S E (.cv y))))
  have p0029 :=
    @g_a1i (.classEq (syn_chnwcutcode S E (.cv y)) (syn_cop (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) p0028
  have p0030 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)) (syn_cop (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) p0027 p0029
  have p0031 :=
    @g_opth (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
  have p0032 :=
    @g_sylib (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_cop (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) p0030 p0031
  have p0033 :=
    @g_simpl (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) p0032 p0033
  have p0035 :=
    @g_isoeq3 (syn_cdm (.cv f)) (syn_crn (.cv f)) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.cv f)
  have p0036 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cdm (.cv f)) (syn_crn (.cv f)))) p0034 p0035
  have p0037 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0022 p0036
  have p0038 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))
  have p0039 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0040 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) p0038 p0039
  have p0041 :=
    @g_simpl (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0042 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) p0040 p0041
  have p0043 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x))))
  have p0044 :=
    @g_a1i (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) p0043
  have p0045 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0042 p0044
  have p0046 :=
    @g_opth (.cv r) (syn_cdm (.cv f)) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0047 :=
    @g_sylib (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classEq (.cv r) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0045 p0046
  have p0048 :=
    @g_simpr (.classEq (.cv r) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0049 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classEq (.cv r) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0047 p0048
  have p0050 :=
    @g_isoeq4 (syn_cdm (.cv f)) (syn_crn (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.cv f)
  have p0051 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classEq (syn_cdm (.cv f)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_crn (.cv f)))) p0049 p0050
  have p0052 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_crn (.cv f))) p0037 p0051
  have p0053 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))
  have p0054 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0055 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) p0053 p0054
  have p0056 :=
    @g_simpr (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0057 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))) p0055 p0056
  have p0058 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode S E (.cv y))))
  have p0059 :=
    @g_a1i (.classEq (syn_chnwcutcode S E (.cv y)) (syn_cop (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) p0058
  have p0060 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)) (syn_cop (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) p0057 p0059
  have p0061 :=
    @g_opth (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
  have p0062 :=
    @g_sylib (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_cop (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) p0060 p0061
  have p0063 :=
    @g_simpr (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0064 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) p0062 p0063
  have p0065 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (.cv f)
  have p0066 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classEq (syn_crn (.cv f)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) p0064 p0065
  have p0067 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) p0052 p0066
  have p0068 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) p0008 p0067
  have p0069 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classMem (.cv y) E) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) p0005 p0068
  have p0070 :=
    @g_rspe (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))) y E
  have p0071 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classMem (.cv y) E) (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) p0069 p0070
  have p0072 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classMem (.cv x) D) (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) p0002 p0071
  have p0073 :=
    @g_rspe (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) x D
  have p0074 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wa (.classMem (.cv x) D) (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (syn_wrex x D (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) p0072 p0073
  have p0075 :=
    @g_elwecutiso x y D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0076 :=
    @g_biimpri (.classMem (.cv f) (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) p0075
  have p0077 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (syn_wrex x D (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))) (.classMem (.cv f) (syn_cwecutiso R D S E)) p0074 p0076
  exact p0077

#print axioms g_wecutisogenfixedrev

end NFChoice.DirectNominalPrf.WPPReplay
