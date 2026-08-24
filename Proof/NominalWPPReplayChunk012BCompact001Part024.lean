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
import NominalWPPReplayChunk012BCompact001Part023

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

noncomputable def g_ins2exg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cins2 A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_cins2] using (Nominal.classEqRefl (syn_cins2 A)))
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_txpexg (syn_cvv) A (syn_cvv) V
  have p0003 :=
    @g_mpan (.classMem (syn_cvv) (syn_cvv)) (.classMem A V) (.classMem (syn_ctxp (syn_cvv) A) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_cins2 A) (syn_ctxp (syn_cvv) A) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_ins3exg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cins3 A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_cins3] using (Nominal.classEqRefl (syn_cins3 A)))
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_txpexg A (syn_cvv) V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem A V) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_ctxp A (syn_cvv)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_cins3 A) (syn_ctxp A (syn_cvv)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_ins2ex
    (A : Class) (hyp_insex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins2 A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ins2exg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_insex_1 p0000
  exact p0001

noncomputable def g_ins3ex
    (A : Class) (hyp_insex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins3 A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ins3exg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_insex_1 p0000
  exact p0001

noncomputable def g_ins4ex
    (A : Class) (hyp_insex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins4 A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cins4] using (Nominal.classEqRefl (syn_cins4 A)))
  have p0001 :=
    @g_n_1stex
  have p0002 :=
    @g_n_1stex
  have p0003 :=
    @g_n_2ndex
  have p0004 :=
    @g_coex (syn_c1st) (syn_c2nd) p0002 p0003
  have p0005 :=
    @g_n_2ndex
  have p0006 :=
    @g_coex (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd) p0004 p0005
  have p0007 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) p0004 p0006
  have p0008 :=
    @g_txpex (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) p0001 p0007
  have p0009 :=
    @g_cnvex (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))) p0008
  have p0010 :=
    @g_imaex (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) A p0009 hyp_insex_1
  have p0011 :=
    @g_eqeltri (syn_cins4 A) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) A) (syn_cvv) p0000 p0010
  exact p0011

noncomputable def g_imageexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cimage A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_cimage] using (Nominal.classEqRefl (syn_cimage A)))
  have p0001 :=
    @g_siexg A V
  have p0002 :=
    @g_cnvexg (syn_csi A) (syn_cvv)
  have p0003 :=
    @g_ssetex
  have p0004 :=
    @g_coexg (syn_csset) (syn_ccnv (syn_csi A)) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_mpan (.classMem (syn_csset) (syn_cvv)) (.classMem (syn_ccnv (syn_csi A)) (syn_cvv)) (.classMem (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_n_3syl (.classMem A V) (.classMem (syn_csi A) (syn_cvv)) (.classMem (syn_ccnv (syn_csi A)) (syn_cvv)) (.classMem (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv)) p0001 p0002 p0005
  have p0007 :=
    @g_ins3exg (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv)
  have p0008 :=
    @g_ssetex
  have p0009 :=
    @g_ins2ex (syn_csset) p0008
  have p0010 :=
    @g_symdifexg (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_mpan (.classMem (syn_cins2 (syn_csset)) (syn_cvv)) (.classMem (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cvv)) (.classMem (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_n_3syl (.classMem A V) (.classMem (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv)) (.classMem (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cvv)) (.classMem (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cvv)) p0006 p0007 p0011
  have p0013 :=
    @g_n_1cex
  have p0014 :=
    @g_imaexg (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_mpan2 (.classMem (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cvv)) (.classMem (syn_c1c) (syn_cvv)) (.classMem (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c)) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_complexg (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c)) (syn_cvv)
  have p0017 :=
    @g_n_3syl (.classMem A V) (.classMem (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cvv)) (.classMem (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c)) (syn_cvv)) (.classMem (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c))) (syn_cvv)) p0012 p0015 p0016
  have p0018 :=
    @g_syl5eqel (.classMem A V) (syn_cimage A) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c))) (syn_cvv) p0000 p0017
  exact p0018

noncomputable def g_imageex
    (A : Class) (hyp_imageex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cimage A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_imageexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_imageex_1 p0000
  exact p0001

noncomputable def g_dmtxp
    (R : Class) (S : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_ctxp R S)) (syn_cin (syn_cdm R) (syn_cdm S))) := by
  let proofSupport : Finset Var := R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_S : p ∉ S.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_p_ne_y : p ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_p : y ≠ p :=
    Ne.symm fresh_p_ne_y
  have fresh_p_ne_z : p ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_p : z ≠ p :=
    Ne.symm fresh_p_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0010 : p ∉ ((syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_R, fresh_p_ne_z, fresh_p_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((syn_ctxp R S)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, fresh_p_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_wbr (.cv x) R (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_wbr (.cv x) S (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_cdm (syn_ctxp R S))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((syn_cin (syn_cdm R) (syn_cdm S))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brtxp y z (.cv x) (.cv p) R S dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0001 :=
    @g_exbii (syn_wbr (.cv x) (syn_ctxp R S) (.cv p)) (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))) p p0000
  have p0002 :=
    @g_exrot3 (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) p y z
  have p0003 :=
    @g_bitri (syn_wex p (syn_wbr (.cv x) (syn_ctxp R S) (.cv p))) (syn_wex p (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))) (syn_wex y (syn_wex z (syn_wex p (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))) p0001 p0002
  have p0004 :=
    @g_n_3anass (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))
  have p0005 :=
    @g_exbii (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))) p p0004
  have p0006 :=
    @g_n_19_41v (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) p dv_cache_0010
  have p0007 :=
    @g_bitri (syn_wex p (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))) (syn_wa (syn_wex p (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))) p0005 p0006
  have p0008 :=
    @g_vex y
  have p0009 :=
    @g_vex z
  have p0010 :=
    @g_opex (.cv y) (.cv z) p0008 p0009
  have p0011 :=
    @g_isseti p (syn_cop (.cv y) (.cv z)) dv_cache_0011 p0010
  have p0012 :=
    @g_biantrur (syn_wex p (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) p0011
  have p0013 :=
    @g_bicomi (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) (syn_wa (syn_wex p (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))) p0012
  have p0014 :=
    @g_bitri (syn_wex p (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))) (syn_wa (syn_wex p (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) p0007 p0013
  have p0015 :=
    @g_n_2exbii (syn_wex p (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) y z p0014
  have p0016 :=
    @g_bitri (syn_wex p (syn_wbr (.cv x) (syn_ctxp R S) (.cv p))) (syn_wex y (syn_wex z (syn_wex p (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))) (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))) p0003 p0015
  have p0017 :=
    @g_eldm p (.cv x) (syn_ctxp R S) dv_cache_0012 dv_cache_0013
  have p0018 :=
    @g_elin (.cv x) (syn_cdm R) (syn_cdm S)
  have p0019 :=
    @g_eldm y (.cv x) R dv_cache_0001 dv_cache_0005
  have p0020 :=
    @g_eldm z (.cv x) S dv_cache_0002 dv_cache_0008
  have p0021 :=
    @g_anbi12i (.classMem (.cv x) (syn_cdm R)) (syn_wex y (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv x) (syn_cdm S)) (syn_wex z (syn_wbr (.cv x) S (.cv z))) p0019 p0020
  have p0022 :=
    @g_eeanv (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)) y z dv_cache_0014 dv_cache_0015
  have p0023 :=
    @g_bicomi (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))) (syn_wa (syn_wex y (syn_wbr (.cv x) R (.cv y))) (syn_wex z (syn_wbr (.cv x) S (.cv z)))) p0022
  have p0024 :=
    @g_bitri (syn_wa (.classMem (.cv x) (syn_cdm R)) (.classMem (.cv x) (syn_cdm S))) (syn_wa (syn_wex y (syn_wbr (.cv x) R (.cv y))) (syn_wex z (syn_wbr (.cv x) S (.cv z)))) (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))) p0021 p0023
  have p0025 :=
    @g_bitri (.classMem (.cv x) (syn_cin (syn_cdm R) (syn_cdm S))) (syn_wa (.classMem (.cv x) (syn_cdm R)) (.classMem (.cv x) (syn_cdm S))) (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))) p0018 p0024
  have p0026 :=
    @g_n_3bitr4i (syn_wex p (syn_wbr (.cv x) (syn_ctxp R S) (.cv p))) (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))) (.classMem (.cv x) (syn_cdm (syn_ctxp R S))) (.classMem (.cv x) (syn_cin (syn_cdm R) (syn_cdm S))) p0016 p0017 p0025
  have p0027 :=
    @g_eqriv x (syn_cdm (syn_ctxp R S)) (syn_cin (syn_cdm R) (syn_cdm S)) dv_cache_0016 dv_cache_0017 p0026
  exact p0027

#print axioms g_dmtxp

end NFChoice.DirectNominalPrf.WPPReplay
