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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk010Compact001Part021

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

noncomputable def g_vfinspnn
     :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (syn_wss (syn_cspfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_wne (.cv z) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cdif (syn_cnnc) (syn_csn (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cdif (syn_cnnc) (syn_csn (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have p0000 :=
    @g_vvex
  have p0001 :=
    @g_ncfinprop (syn_cvv) (syn_cvv)
  have p0002 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))) p0000 p0001
  have p0003 :=
    @g_ne0i (syn_cncfin (syn_cvv)) (syn_cvv)
  have p0004 :=
    @g_anim2i (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) (syn_wne (syn_cncfin (syn_cvv)) (syn_c0)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) p0003
  have p0005 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (syn_wne (syn_cncfin (syn_cvv)) (syn_c0))) p0002 p0004
  have p0006 :=
    @g_eldifsn (syn_cncfin (syn_cvv)) (syn_cnnc) (syn_c0)
  have p0007 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin)) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (syn_wne (syn_cncfin (syn_cvv)) (syn_c0))) (.classMem (syn_cncfin (syn_cvv)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0005 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (.cv z) (.cv x) y dv_cache_0001 dv_cache_0002
  have p0009 :=
    @g_ne0i (.cv z) (syn_cpw1 (.cv y))
  have p0010 :=
    @g_adantr (.classMem (syn_cpw1 (.cv y)) (.cv z)) (syn_wne (.cv z) (syn_c0)) (.classMem (syn_cpw (.cv y)) (.cv x)) p0009
  have p0011 :=
    @g_exlimiv (syn_wa (.classMem (syn_cpw1 (.cv y)) (.cv z)) (.classMem (syn_cpw (.cv y)) (.cv x))) (syn_wne (.cv z) (syn_c0)) y dv_cache_0003 p0010
  have p0012 :=
    @g_eldifsn (.cv z) (syn_cnnc) (syn_c0)
  have p0013 :=
    @g_biimpri (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (syn_wa (.classMem (.cv z) (syn_cnnc)) (syn_wne (.cv z) (syn_c0))) p0012
  have p0014 :=
    @g_sylan2 (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) (.cv z)) (.classMem (syn_cpw (.cv y)) (.cv x)))) (.classMem (.cv z) (syn_cnnc)) (syn_wne (.cv z) (syn_c0)) (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0011 p0013
  have p0015 :=
    @g_n_3adant2 (.classMem (.cv z) (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) (.cv z)) (.classMem (syn_cpw (.cv y)) (.cv x)))) (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (.classMem (.cv x) (syn_cnnc)) p0014
  have p0016 :=
    @g_sylbi (syn_wsfin (.cv z) (.cv x)) (syn_w3a (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) (.cv z)) (.classMem (syn_cpw (.cv y)) (.cv x))))) (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0008 p0015
  have p0017 :=
    @g_adantl (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0016
  have p0018 :=
    Nominal.gen p0017 z
  have p0019 :=
    @g_rgenw (.all z (.imp (syn_wa (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))))) x (syn_cspfin) p0018
  have p0020 :=
    @g_nncex
  have p0021 :=
    @g_snex (syn_c0)
  have p0022 :=
    @g_difex (syn_cnnc) (syn_csn (syn_c0)) p0020 p0021
  have p0023 :=
    @g_spfininduct x z (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0024 :=
    @g_mp3an1 (.classMem (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (syn_wral x (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))))) (syn_wss (syn_cspfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0022 p0023
  have p0025 :=
    @g_sylancl (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cvv)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (syn_wral x (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))))) (syn_wss (syn_cspfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0007 p0019 p0024
  exact p0025

noncomputable def g_n_1cvsfin
     :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv)))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : a ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((syn_wa (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) (.classMem (syn_cvv) (syn_cncfin (syn_cvv))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((syn_cncfin (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((syn_cncfin (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_ncfinprop (syn_c1c) (syn_cvv)
  have p0002 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv))) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0001
  have p0003 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) p0000 p0002
  have p0004 :=
    @g_vvex
  have p0005 :=
    @g_ncfinprop (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv))) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0005
  have p0007 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) p0004 p0006
  have p0008 :=
    @g_n_1cex
  have p0009 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c)))) p0008 p0001
  have p0010 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0009
  have p0011 :=
    @g_vvex
  have p0012 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))) p0011 p0005
  have p0013 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0012
  have p0014 :=
    @g_vvex
  have p0015 :=
    @g_pw1eq (.cv a) (syn_cvv)
  have p0016 :=
    @g_df1c2
  have p0017 :=
    @g_syl6eqr (.classEq (.cv a) (syn_cvv)) (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cvv)) (syn_c1c) p0015 p0016
  have p0018 :=
    @g_eleq1d (.classEq (.cv a) (syn_cvv)) (syn_cpw1 (.cv a)) (syn_c1c) (syn_cncfin (syn_c1c)) p0017
  have p0019 :=
    @g_pweq (.cv a) (syn_cvv)
  have p0020 :=
    @g_pwv
  have p0021 :=
    @g_syl6eq (.classEq (.cv a) (syn_cvv)) (syn_cpw (.cv a)) (syn_cpw (syn_cvv)) (syn_cvv) p0019 p0020
  have p0022 :=
    @g_eleq1d (.classEq (.cv a) (syn_cvv)) (syn_cpw (.cv a)) (syn_cvv) (syn_cncfin (syn_cvv)) p0021
  have p0023 :=
    @g_anbi12d (.classEq (.cv a) (syn_cvv)) (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c))) (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv))) (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0018 p0022
  have p0024 :=
    @g_spcev (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv)))) (syn_wa (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))) a (syn_cvv) dv_cache_0001 dv_cache_0002 p0014 p0023
  have p0025 :=
    @g_syl2anc (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv))))) p0010 p0013 p0024
  have p0026 :=
    @g_n_3jca (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv))))) p0003 p0007 p0025
  have p0027 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv)) a dv_cache_0003 dv_cache_0004
  have p0028 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin)) (syn_w3a (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv)))))) (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) p0026 p0027
  exact p0028

noncomputable def g_n_1cspfin
     :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_c1c)) (syn_cspfin))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_ncvspfin
  have p0001 :=
    @g_n_1cvsfin
  have p0002 :=
    @g_spfinsfincl (syn_cncfin (syn_cvv)) (syn_cncfin (syn_c1c))
  have p0003 :=
    @g_sylancr (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin)) (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (.classMem (syn_cncfin (syn_c1c)) (syn_cspfin)) p0000 p0001 p0002
  exact p0003

noncomputable def g_tncveqnc1fin
     :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_vvex
  have p0001 :=
    @g_ncfintfin (syn_cvv) (syn_cvv)
  have p0002 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv)) (.classEq (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_cpw1 (syn_cvv)))) p0000 p0001
  have p0003 :=
    @g_df1c2
  have p0004 :=
    @g_ncfineq (syn_c1c) (syn_cpw1 (syn_cvv))
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_syl6eqr (.classMem (syn_cvv) (syn_cfin)) (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_cpw1 (syn_cvv))) (syn_cncfin (syn_c1c)) p0002 p0005
  exact p0006

noncomputable def g_t1csfin1c
     :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cncfin (syn_c1c)))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cvsfin
  have p0001 :=
    @g_sfintfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))
  have p0002 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_ctfin (syn_cncfin (syn_cvv)))) p0000 p0001
  have p0003 :=
    @g_tncveqnc1fin
  have p0004 :=
    @g_sfineq2 (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)) (syn_ctfin (syn_cncfin (syn_c1c)))
  have p0005 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c))) (syn_wb (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_ctfin (syn_cncfin (syn_cvv)))) (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cncfin (syn_c1c)))) p0003 p0004
  have p0006 :=
    @g_mpbid (.classMem (syn_cvv) (syn_cfin)) (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_ctfin (syn_cncfin (syn_cvv)))) (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cncfin (syn_c1c))) p0002 p0005
  exact p0006

noncomputable def g_vfintle
    (N : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin))) := by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have dv_cache_0001 : a ∉ (N).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Wff.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n0 a N dv_cache_0001
  have p0001 :=
    @g_simp2 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (.cv a) N)
  have p0002 :=
    @g_ncfinprop (.cv a) N
  have p0003 :=
    @g_n_3adant2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv a) N) (syn_wa (.classMem (syn_cncfin (.cv a)) (syn_cnnc)) (.classMem (.cv a) (syn_cncfin (.cv a)))) (.classMem N (syn_cnnc)) p0002
  have p0004 :=
    @g_simpld (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cncfin (.cv a)) (syn_cnnc)) (.classMem (.cv a) (syn_cncfin (.cv a))) p0003
  have p0005 :=
    @g_simp3 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (.cv a) N)
  have p0006 :=
    @g_simprd (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cncfin (.cv a)) (syn_cnnc)) (.classMem (.cv a) (syn_cncfin (.cv a))) p0003
  have p0007 :=
    @g_nnceleq (.cv a) N (syn_cncfin (.cv a))
  have p0008 :=
    @g_syl22anc (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem N (syn_cnnc)) (.classMem (syn_cncfin (.cv a)) (syn_cnnc)) (.classMem (.cv a) N) (.classMem (.cv a) (syn_cncfin (.cv a))) (.classEq N (syn_cncfin (.cv a))) p0001 p0004 p0005 p0006 p0007
  have p0009 :=
    @g_n_3expia (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (.cv a) N) (.classEq N (syn_cncfin (.cv a))) p0008
  have p0010 :=
    @g_simpr (.classMem (syn_cvv) (syn_cfin)) (.classEq N (syn_cncfin (.cv a)))
  have p0011 :=
    @g_uncompl (.cv a)
  have p0012 :=
    @g_ncfineq (syn_cun (.cv a) (syn_ccompl (.cv a))) (syn_cvv)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_vex a
  have p0015 :=
    @g_complex (.cv a) p0014
  have p0016 :=
    @g_incompl (.cv a)
  have p0017 :=
    @g_ncfindi (.cv a) (syn_ccompl (.cv a)) (syn_cvv) (syn_cvv)
  have p0018 :=
    @g_mp3an23 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv a) (syn_cvv))) (.classMem (syn_ccompl (.cv a)) (syn_cvv)) (.classEq (syn_cin (.cv a) (syn_ccompl (.cv a))) (syn_c0)) (.classEq (syn_cncfin (syn_cun (.cv a) (syn_ccompl (.cv a)))) (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))))) p0015 p0016 p0017
  have p0019 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv a) (syn_cvv)) (.classEq (syn_cncfin (syn_cun (.cv a) (syn_ccompl (.cv a)))) (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))))) p0014 p0018
  have p0020 :=
    @g_syl5eqr (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cun (.cv a) (syn_ccompl (.cv a)))) (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))) p0013 p0019
  have p0021 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cncfin (syn_cvv)) (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))))) (.classEq N (syn_cncfin (.cv a))) p0020
  have p0022 :=
    @g_opkeq12d (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classEq N (syn_cncfin (.cv a)))) N (syn_cncfin (.cv a)) (syn_cncfin (syn_cvv)) (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))) p0010 p0021
  have p0023 :=
    @g_ncfinex (.cv a)
  have p0024 :=
    @g_ncfinprop (syn_ccompl (.cv a)) (syn_cvv)
  have p0025 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ccompl (.cv a)) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_ccompl (.cv a))) (syn_cnnc)) (.classMem (syn_ccompl (.cv a)) (syn_cncfin (syn_ccompl (.cv a))))) p0015 p0024
  have p0026 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_ccompl (.cv a))) (syn_cnnc)) (.classMem (syn_ccompl (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))) p0025
  have p0027 :=
    @g_lefinaddc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))) (syn_cvv)
  have p0028 :=
    @g_sylancr (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (.cv a)) (syn_cvv)) (.classMem (syn_cncfin (syn_ccompl (.cv a))) (syn_cnnc)) (.classMem (syn_copk (syn_cncfin (.cv a)) (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))))) (syn_clefin)) p0023 p0026 p0027
  have p0029 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_copk (syn_cncfin (.cv a)) (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))))) (syn_clefin)) (.classEq N (syn_cncfin (.cv a))) p0028
  have p0030 :=
    @g_eqeltrd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classEq N (syn_cncfin (.cv a)))) (syn_copk N (syn_cncfin (syn_cvv))) (syn_copk (syn_cncfin (.cv a)) (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))))) (syn_clefin) p0022 p0029
  have p0031 :=
    @g_ex (.classMem (syn_cvv) (syn_cfin)) (.classEq N (syn_cncfin (.cv a))) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) p0030
  have p0032 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin)) (.imp (.classEq N (syn_cncfin (.cv a))) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin))) (.classMem N (syn_cnnc)) p0031
  have p0033 :=
    @g_syld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))) (.classMem (.cv a) N) (.classEq N (syn_cncfin (.cv a))) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) p0009 p0032
  have p0034 :=
    @g_exlimdv (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))) (.classMem (.cv a) N) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) a dv_cache_0002 dv_cache_0003 p0033
  have p0035 :=
    @g_syl5bi (syn_wne N (syn_c0)) (syn_wex a (.classMem (.cv a) N)) (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) p0000 p0034
  have p0036 :=
    @g_n_3impia (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) p0035
  have p0037 :=
    @g_simp2 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))
  have p0038 :=
    @g_vvex
  have p0039 :=
    @g_ncfinprop (syn_cvv) (syn_cvv)
  have p0040 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))) p0038 p0039
  have p0041 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))) (syn_wne N (syn_c0)) p0040
  have p0042 :=
    @g_simpld (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0041
  have p0043 :=
    @g_tfinlefin N (syn_cncfin (syn_cvv))
  have p0044 :=
    @g_syl2anc (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem N (syn_cnnc)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (syn_wb (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin (syn_cncfin (syn_cvv)))) (syn_clefin))) p0037 p0042 p0043
  have p0045 :=
    @g_tncveqnc1fin
  have p0046 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classEq (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c))) (syn_wne N (syn_c0)) p0045
  have p0047 :=
    @g_opkeq2d (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)) (syn_ctfin N) p0046
  have p0048 :=
    @g_eleq1d (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (syn_copk (syn_ctfin N) (syn_ctfin (syn_cncfin (syn_cvv)))) (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin) p0047
  have p0049 :=
    @g_bitrd (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin (syn_cncfin (syn_cvv)))) (syn_clefin)) (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin)) p0044 p0048
  have p0050 :=
    @g_mpbid (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin)) p0036 p0049
  exact p0050

noncomputable def g_vfin1cltv
     :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_uncompl (syn_c1c)
  have p0001 :=
    @g_ncfineq (syn_cun (syn_c1c) (syn_ccompl (syn_c1c))) (syn_cvv)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_n_1cex
  have p0004 :=
    @g_n_1cex
  have p0005 :=
    @g_complex (syn_c1c) p0004
  have p0006 :=
    @g_incompl (syn_c1c)
  have p0007 :=
    @g_ncfindi (syn_c1c) (syn_ccompl (syn_c1c)) (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_mp3an23 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv))) (.classMem (syn_ccompl (syn_c1c)) (syn_cvv)) (.classEq (syn_cin (syn_c1c) (syn_ccompl (syn_c1c))) (syn_c0)) (.classEq (syn_cncfin (syn_cun (syn_c1c) (syn_ccompl (syn_c1c)))) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) p0005 p0006 p0007
  have p0009 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv)) (.classEq (syn_cncfin (syn_cun (syn_c1c) (syn_ccompl (syn_c1c)))) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) p0003 p0008
  have p0010 :=
    @g_syl5reqr (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cun (syn_c1c) (syn_ccompl (syn_c1c)))) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0002 p0009
  have p0011 :=
    @g_opkeq2d (.classMem (syn_cvv) (syn_cfin)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) (syn_cncfin (syn_cvv)) (syn_cncfin (syn_c1c)) p0010
  have p0012 :=
    @g_n_0nel1c
  have p0013 :=
    @g_n_0ex
  have p0014 :=
    @g_elcompl (syn_c0) (syn_c1c) p0013
  have p0015 :=
    @g_mpbir (.classMem (syn_c0) (syn_ccompl (syn_c1c))) (.neg (.classMem (syn_c0) (syn_c1c))) p0012 p0014
  have p0016 :=
    @g_n0i (syn_ccompl (syn_c1c)) (syn_c0)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_ncfinprop (syn_ccompl (syn_c1c)) (syn_cvv)
  have p0019 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ccompl (syn_c1c)) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc)) (.classMem (syn_ccompl (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) p0005 p0018
  have p0020 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc)) (.classMem (syn_ccompl (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0019
  have p0021 :=
    @g_eleq2 (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c))) (syn_ccompl (syn_c1c))
  have p0022 :=
    @g_syl5ibrcom (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ccompl (syn_c1c)) (syn_c0c)) (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c)))) (.classMem (syn_ccompl (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0020 p0021
  have p0023 :=
    @g_el0c (syn_ccompl (syn_c1c))
  have p0024 :=
    @g_syl6ib (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c)))) (.classMem (syn_ccompl (syn_c1c)) (syn_c0c)) (.classEq (syn_ccompl (syn_c1c)) (syn_c0)) p0022 p0023
  have p0025 :=
    @g_mtoi (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c)))) (.classEq (syn_ccompl (syn_c1c)) (syn_c0)) p0017 p0024
  have p0026 :=
    @g_addcid1 (syn_cncfin (syn_c1c))
  have p0027 :=
    @g_eqeq1i (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0026
  have p0028 :=
    @g_n_1cex
  have p0029 :=
    @g_ncfinprop (syn_c1c) (syn_cvv)
  have p0030 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c)))) p0028 p0029
  have p0031 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0030
  have p0032 :=
    @g_peano1
  have p0033 :=
    @g_a1i (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_cvv) (syn_cfin)) p0032
  have p0034 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc)) (.classMem (syn_ccompl (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0019
  have p0035 :=
    @g_a1i (.classEq (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_cncfin (syn_c1c))) (.classMem (syn_cvv) (syn_cfin)) p0026
  have p0036 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0030
  have p0037 :=
    @g_ne0i (syn_cncfin (syn_c1c)) (syn_c1c)
  have p0038 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) (syn_wne (syn_cncfin (syn_c1c)) (syn_c0)) p0036 p0037
  have p0039 :=
    @g_eqnetrd (.classMem (syn_cvv) (syn_cfin)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_cncfin (syn_c1c)) (syn_c0) p0035 p0038
  have p0040 :=
    @g_preaddccan2 (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cncfin (syn_c1c)) (syn_c0c)
  have p0041 :=
    @g_syl31anc (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc)) (syn_wne (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_c0)) (syn_wb (.classEq (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c))))) p0031 p0033 p0034 p0039 p0040
  have p0042 :=
    @g_syl5bbr (.classEq (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (.classEq (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c)))) p0027 p0041
  have p0043 :=
    @g_mtbird (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c)))) p0025 p0042
  have p0044 :=
    @g_ncfinex (syn_c1c)
  have p0045 :=
    @g_lefinaddc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cvv)
  have p0046 :=
    @g_sylancr (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_c1c)) (syn_cvv)) (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc)) (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_clefin)) p0044 p0034 p0045
  have p0047 :=
    @g_ncfinex (syn_ccompl (syn_c1c))
  have p0048 :=
    @g_addcex (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))) p0044 p0047
  have p0049 :=
    @g_lefinlteq (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) (syn_cvv) (syn_cvv)
  have p0050 :=
    @g_mp3an12 (.classMem (syn_cncfin (syn_c1c)) (syn_cvv)) (.classMem (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) (syn_cvv)) (syn_wne (syn_cncfin (syn_c1c)) (syn_c0)) (syn_wb (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_clefin)) (syn_wo (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin)) (.classEq (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))))) p0044 p0048 p0049
  have p0051 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (syn_wne (syn_cncfin (syn_c1c)) (syn_c0)) (syn_wb (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_clefin)) (syn_wo (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin)) (.classEq (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))))) p0038 p0050
  have p0052 :=
    @g_mpbid (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_clefin)) (syn_wo (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin)) (.classEq (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))) p0046 p0051
  have p0053 :=
    @g_orcomd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin)) (.classEq (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) p0052
  have p0054 :=
    @g_ord (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin)) p0053
  have p0055 :=
    @g_mpd (.classMem (syn_cvv) (syn_cfin)) (.neg (.classEq (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))) (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin)) p0043 p0054
  have p0056 :=
    @g_eqeltrrd (.classMem (syn_cvv) (syn_cfin)) (syn_copk (syn_cncfin (syn_c1c)) (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin) p0011 p0055
  exact p0056

noncomputable def g_vfinncvntnn
    (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))) (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv)))) := by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have dv_cache_0001 : a ∉ (N).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vvex
  have p0001 :=
    @g_ncfinprop (syn_cvv) (syn_cvv)
  have p0002 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))) p0000 p0001
  have p0003 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0002
  have p0004 :=
    @g_ne0i (syn_cncfin (syn_cvv)) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) (syn_wne (syn_cncfin (syn_cvv)) (syn_c0)) p0003 p0004
  have p0006 :=
    @g_necomd (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cvv)) (syn_c0) p0005
  have p0007 :=
    @g_tfineq N (syn_c0)
  have p0008 :=
    @g_tfinnul
  have p0009 :=
    @g_syl6eq (.classEq N (syn_c0)) (syn_ctfin N) (syn_ctfin (syn_c0)) (syn_c0) p0007 p0008
  have p0010 :=
    @g_neeq1d (.classEq N (syn_c0)) (syn_ctfin N) (syn_c0) (syn_cncfin (syn_cvv)) p0009
  have p0011 :=
    @g_syl5ibr (.classMem (syn_cvv) (syn_cfin)) (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) (.classEq N (syn_c0)) (syn_wne (syn_c0) (syn_cncfin (syn_cvv))) p0006 p0010
  have p0012 :=
    @g_adantrd (.classEq N (syn_c0)) (.classMem (syn_cvv) (syn_cfin)) (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) (.classMem N (syn_cnnc)) p0011
  have p0013 :=
    @g_vvex
  have p0014 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv))) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0001
  have p0015 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) p0013 p0014
  have p0016 :=
    @g_ltfinirr (syn_cncfin (syn_cvv))
  have p0017 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.neg (.classMem (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin))) p0015 p0016
  have p0018 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.neg (.classMem (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin))) (syn_wne N (syn_c0)) p0017
  have p0019 :=
    @g_vfintle N
  have p0020 :=
    @g_vfin1cltv
  have p0021 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin)) (syn_wne N (syn_c0)) p0020
  have p0022 :=
    @g_tfinprop N a dv_cache_0001
  have p0023 :=
    @g_simpld (syn_wa (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) p0022
  have p0024 :=
    @g_n_3adant1 (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) (.classMem (syn_ctfin N) (syn_cnnc)) (.classMem (syn_cvv) (syn_cfin)) p0023
  have p0025 :=
    @g_n_1cex
  have p0026 :=
    @g_ncfinprop (syn_c1c) (syn_cvv)
  have p0027 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv))) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0026
  have p0028 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) p0025 p0027
  have p0029 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (syn_wne N (syn_c0)) p0028
  have p0030 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (syn_wne N (syn_c0)) p0015
  have p0031 :=
    @g_leltfintr (syn_ctfin N) (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))
  have p0032 :=
    @g_syl3anc (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_ctfin N) (syn_cnnc)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (.imp (syn_wa (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin)) (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin))) (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_cvv))) (syn_cltfin))) p0024 p0029 p0030 p0031
  have p0033 :=
    @g_mp2and (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin)) (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin)) (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_cvv))) (syn_cltfin)) p0019 p0021 p0032
  have p0034 :=
    @g_opkeq1 (syn_ctfin N) (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))
  have p0035 :=
    @g_eleq1d (.classEq (syn_ctfin N) (syn_cncfin (syn_cvv))) (syn_copk (syn_ctfin N) (syn_cncfin (syn_cvv))) (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin) p0034
  have p0036 :=
    @g_syl5ibcom (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_cvv))) (syn_cltfin)) (.classEq (syn_ctfin N) (syn_cncfin (syn_cvv))) (.classMem (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin)) p0033 p0035
  have p0037 :=
    @g_mtod (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classEq (syn_ctfin N) (syn_cncfin (syn_cvv))) (.classMem (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin)) p0018 p0036
  have p0038 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv)))))
  have p0039 :=
    @g_sylibr (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.neg (.classEq (syn_ctfin N) (syn_cncfin (syn_cvv)))) (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) p0037 p0038
  have p0040 :=
    @g_n_3expa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) p0039
  have p0041 :=
    @g_expcom (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))) (syn_wne N (syn_c0)) (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) p0040
  have p0042 :=
    @g_pm2_61ine (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))) (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv)))) N (syn_c0) p0012 p0041
  exact p0042

noncomputable def g_vfinncvntsp
    (x : Var) (a : Var) (dv_a_x : a ≠ x) :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (.neg (.classMem (syn_cncfin (syn_cvv)) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({a} : Finset Var)
  have dv_cache_0001 : x ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv a) (syn_cncfin (syn_cvv)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((syn_cncfin (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_a_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vfinspnn
  have p0001 :=
    @g_difss (syn_cnnc) (syn_csn (syn_c0))
  have p0002 :=
    @g_syl6ss (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cnnc) p0000 p0001
  have p0003 :=
    @g_sselda (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin) (syn_cnnc) (.cv x) p0002
  have p0004 :=
    @g_vfinncvntnn (.cv x)
  have p0005 :=
    @g_syldan (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv x) (syn_cnnc)) (syn_wne (syn_ctfin (.cv x)) (syn_cncfin (syn_cvv))) p0003 p0004
  have p0006 :=
    @g_necomd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv x) (syn_cspfin))) (syn_ctfin (.cv x)) (syn_cncfin (syn_cvv)) p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x)))))
  have p0008 :=
    @g_sylib (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv x) (syn_cspfin))) (syn_wne (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))) (.neg (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x)))) p0006 p0007
  have p0009 :=
    @g_nrexdv (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0001 p0008
  have p0010 :=
    @g_ncfinex (syn_cvv)
  have p0011 :=
    @g_eqeq1 (.cv a) (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))
  have p0012 :=
    @g_rexbidv (.classEq (.cv a) (syn_cncfin (syn_cvv))) (.classEq (.cv a) (syn_ctfin (.cv x))) (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0002 p0011
  have p0013 :=
    @g_elab (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x)))) a (syn_cncfin (syn_cvv)) dv_cache_0003 dv_cache_0004 p0010 p0012
  have p0014 :=
    @g_sylnibr (.classMem (syn_cvv) (syn_cfin)) (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x)))) (.classMem (syn_cncfin (syn_cvv)) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) p0009 p0013
  exact p0014

#print axioms g_vfinncvntsp

end NFChoice.DirectNominalPrf.WPPReplay
