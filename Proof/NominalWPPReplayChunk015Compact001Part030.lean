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
import NominalWPPReplayChunk015Compact001Part029

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

noncomputable def g_lnsifnvalg
    (R : Class) (hyp_lnsifnvalg_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classEq (syn_cfv (syn_clnsifn) (syn_csn R)) (syn_csi R))) := by
  let proofSupport : Finset Var := R.fv
  have p0000 :=
    @g_lnsifnrawval R hyp_lnsifnvalg_1
  have p0001 :=
    @g_a1i (.classEq (syn_cfv (syn_clnsifn) (syn_csn R)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0000
  have p0002 :=
    @g_lnsifnimageexactg R
  have p0003 :=
    @g_eqtrd (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (syn_cfv (syn_clnsifn) (syn_csn R)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (syn_csi R) p0001 p0002
  exact p0003

noncomputable def g_lnpwsirelfnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnpwsirelfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_lnsifnfn
  have p0001 :=
    @g_n_1stex
  have p0002 :=
    @g_wppimagefn (syn_c1st) p0001
  have p0003 :=
    @g_fncovv (syn_clnsifn) (syn_cimage (syn_c1st)) p0000 p0002
  have p0004 :=
    (by simpa [syn_clnpwsirelfn] using (Nominal.classEqRefl (syn_clnpwsirelfn)))
  have p0005 :=
    @g_fneq1i (syn_cvv) (syn_clnpwsirelfn) (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_clnpwsirelfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) (syn_cvv)) p0003 p0005
  exact p0006

noncomputable def g_lnpwsirelfnex
     :
    Nominal.NPrf (.classMem (syn_clnpwsirelfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnpwsirelfn] using (Nominal.classEqRefl (syn_clnpwsirelfn)))
  have p0001 :=
    @g_lnsifnex
  have p0002 :=
    @g_n_1stex
  have p0003 :=
    @g_imageex (syn_c1st) p0002
  have p0004 :=
    @g_coex (syn_clnsifn) (syn_cimage (syn_c1st)) p0001 p0003
  have p0005 :=
    @g_eqeltri (syn_clnpwsirelfn) (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) (syn_cvv) p0000 p0004
  exact p0005

noncomputable def g_lnpwsirelfnrawval
    (D : Class) (R : Class) (hyp_lnpwsirelfnrawval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwsirelfnrawval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_clnsifn) (syn_csn R))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint ((syn_csn (syn_cop R D))).fv ((syn_c1st)).fv := by
    exact (show Disjoint ((syn_csn (syn_cop R D))).fv ((syn_c1st)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint (((syn_cop R D)).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 :=
    (by simpa [syn_clnpwsirelfn] using (Nominal.classEqRefl (syn_clnpwsirelfn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_clnpwsirelfn) (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) p0000
  have p0002 :=
    @g_n_1stex
  have p0003 :=
    @g_wppimagefn (syn_c1st) p0002
  have p0004 :=
    @g_snex (syn_cop R D)
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c1st)) (syn_cvv)) (.classMem (syn_csn (syn_cop R D)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_cop R D)) (syn_clnsifn) (syn_cimage (syn_c1st))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_n_1stex
  have p0009 :=
    @g_snex (syn_cop R D)
  have p0010 :=
    @g_wppfvimage (syn_csn (syn_cop R D)) (syn_c1st) dv_cache_0001 p0008 p0009
  have p0011 :=
    @g_dfdm4 (syn_csn (syn_cop R D))
  have p0012 :=
    @g_eqcomi (syn_cdm (syn_csn (syn_cop R D))) (syn_cima (syn_c1st) (syn_csn (syn_cop R D))) p0011
  have p0013 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop R D))) (syn_cima (syn_c1st) (syn_csn (syn_cop R D))) (syn_cdm (syn_csn (syn_cop R D))) p0010 p0012
  have p0014 :=
    @g_dmsnop R D hyp_lnpwsirelfnrawval_2
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop R D))) (syn_cdm (syn_csn (syn_cop R D))) (syn_csn R) p0013 p0014
  have p0016 :=
    @g_fveq2i (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop R D))) (syn_csn R) (syn_clnsifn) p0015
  have p0017 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) (syn_csn (syn_cop R D))) (syn_cfv (syn_clnsifn) (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop R D)))) (syn_cfv (syn_clnsifn) (syn_csn R)) p0007 p0016
  have p0018 :=
    @g_eqtri (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) (syn_csn (syn_cop R D))) (syn_cfv (syn_clnsifn) (syn_csn R)) p0001 p0017
  exact p0018

noncomputable def g_lnpwsirelfnvalg
    (D : Class) (R : Class) (hyp_lnpwsirelfnvalg_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwsirelfnvalg_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classEq (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_csi R))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_lnpwsirelfnrawval D R hyp_lnpwsirelfnvalg_1 hyp_lnpwsirelfnvalg_2
  have p0001 :=
    @g_a1i (.classEq (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_clnsifn) (syn_csn R))) (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0000
  have p0002 :=
    @g_lnsifnvalg R hyp_lnpwsirelfnvalg_1
  have p0003 :=
    @g_eqtrd (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_clnsifn) (syn_csn R)) (syn_csi R) p0001 p0002
  exact p0003

noncomputable def g_pw1subuniss
    (x : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wss (.cv x) (syn_cpw1 A)) (syn_wss (syn_cuni (.cv x)) A)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_uniss (.cv x) (syn_cpw1 A)
  have p0001 :=
    @g_unipw1 A
  have p0002 :=
    @g_sseq2i (syn_cuni (syn_cpw1 A)) A (syn_cuni (.cv x)) p0001
  have p0003 :=
    @g_biimpi (syn_wss (syn_cuni (.cv x)) (syn_cuni (syn_cpw1 A))) (syn_wss (syn_cuni (.cv x)) A) p0002
  have p0004 :=
    @g_syl (syn_wss (.cv x) (syn_cpw1 A)) (syn_wss (syn_cuni (.cv x)) (syn_cuni (syn_cpw1 A))) (syn_wss (syn_cuni (.cv x)) A) p0000 p0003
  exact p0004

noncomputable def g_pw1subunine
    (x : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (syn_wne (syn_cuni (.cv x)) (syn_c0))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_wne (syn_cuni (.cv x)) (syn_c0))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))
  have p0001 :=
    @g_n0 q (.cv x) dv_cache_0001
  have p0002 :=
    @g_biimpi (syn_wne (.cv x) (syn_c0)) (syn_wex q (.classMem (.cv q) (.cv x))) p0001
  have p0003 :=
    @g_syl (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (syn_wne (.cv x) (syn_c0)) (syn_wex q (.classMem (.cv q) (.cv x))) p0000 p0002
  have p0004 :=
    @g_vex q
  have p0005 :=
    @g_uniex (.cv q) p0004
  have p0006 :=
    @g_snid (syn_cuni (.cv q)) p0005
  have p0007 :=
    @g_a1i (.classMem (syn_cuni (.cv q)) (syn_csn (syn_cuni (.cv q)))) (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))) p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))
  have p0009 :=
    @g_simpl (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))) (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) (syn_cpw1 A)) p0008 p0009
  have p0011 :=
    @g_simpr (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))
  have p0012 :=
    @g_sseldd (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))) (.cv x) (syn_cpw1 A) (.cv q) p0010 p0011
  have p0013 :=
    @g_hnwpw1argcl A q
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))) (.classMem (.cv q) (syn_cpw1 A)) (syn_wa (.classMem (syn_cuni (.cv q)) A) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0012 p0013
  have p0015 :=
    @g_simprd (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))) (.classMem (syn_cuni (.cv q)) A) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0014
  have p0016 :=
    @g_eleqtrrd (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))) (syn_cuni (.cv q)) (syn_csn (syn_cuni (.cv q))) (.cv q) p0007 p0015
  have p0017 :=
    @g_simpr (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))
  have p0018 :=
    @g_jca (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))) (.classMem (syn_cuni (.cv q)) (.cv q)) (.classMem (.cv q) (.cv x)) p0016 p0017
  have p0019 :=
    @g_elunii (syn_cuni (.cv q)) (.cv q) (.cv x)
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))) (syn_wa (.classMem (syn_cuni (.cv q)) (.cv q)) (.classMem (.cv q) (.cv x))) (.classMem (syn_cuni (.cv q)) (syn_cuni (.cv x))) p0018 p0019
  have p0021 :=
    @g_ne0i (syn_cuni (.cv x)) (syn_cuni (.cv q))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x))) (.classMem (syn_cuni (.cv q)) (syn_cuni (.cv x))) (syn_wne (syn_cuni (.cv x)) (syn_c0)) p0020 p0021
  have p0023 :=
    @g_exlimddv (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))) (.classMem (.cv q) (.cv x)) (syn_wne (syn_cuni (.cv x)) (syn_c0)) q dv_cache_0002 dv_cache_0003 p0003 p0022
  exact p0023

noncomputable def g_wppreachopfn
    (F : Class) (hyp_wppreachopfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cimage (syn_ccnv F)) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    @g_cnvex F hyp_wppreachopfn_1
  have p0001 :=
    @g_wppimagefn (syn_ccnv F) p0000
  exact p0001

noncomputable def g_wppreachupperex
    (C : Class) :
    Nominal.NPrf (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv
  have p0000 :=
    @g_lecex
  have p0001 :=
    @g_snex C
  have p0002 :=
    @g_imaex (syn_clec) (syn_csn C) p0000 p0001
  exact p0002

noncomputable def g_wppreach0
    (C : Class) (F : Class) (dv_C_F : Disjoint C.fv F.fv) (hyp_wppreachorbitfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_c0c)) (syn_cima (syn_clec) (syn_csn C))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have dv_cache_0001 : Disjoint ((syn_cimage (syn_ccnv F))).fv ((syn_cima (syn_clec) (syn_csn C))).fv := by
    exact (show Disjoint ((syn_cimage (syn_ccnv F))).fv ((syn_cima (syn_clec) (syn_csn C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima]; exact (show Disjoint (((syn_ccnv F)).fv) ((((syn_clec)).fv) ∪ (((syn_csn C)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (((syn_ccnv F)).fv) (((syn_clec)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv]; exact (show Disjoint ((F).fv) (((syn_clec)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec]; exact (show Disjoint ((F).fv) ((∅ : Finset Var)) from (by simp)))))), (show Disjoint (((syn_ccnv F)).fv) (((syn_csn C)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv]; exact (show Disjoint ((F).fv) (((syn_csn C)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (F).fv (C).fv from (by exact dv_C_F.symm))))))⟩))))
  have p0000 :=
    @g_cnvex F hyp_wppreachorbitfn_1
  have p0001 :=
    @g_wppimagefn (syn_ccnv F) p0000
  have p0002 :=
    @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_cnvex F hyp_wppreachorbitfn_1
  have p0005 :=
    @g_imageex (syn_ccnv F) p0004
  have p0006 :=
    @g_elfuns (syn_cimage (syn_ccnv F)) p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (syn_wfun (syn_cimage (syn_ccnv F))) p0003 p0006
  have p0008 :=
    @g_lecex
  have p0009 :=
    @g_snex C
  have p0010 :=
    @g_imaex (syn_clec) (syn_csn C) p0008 p0009
  have p0011 :=
    @g_cnvex F hyp_wppreachorbitfn_1
  have p0012 :=
    @g_wppimagefn (syn_ccnv F) p0011
  have p0013 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0010 p0014
  have p0016 :=
    @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0017 :=
    @g_cnvex F hyp_wppreachorbitfn_1
  have p0018 :=
    @g_wppimagefn (syn_ccnv F) p0017
  have p0019 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0016 p0020
  have p0022 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F)))) (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F)))) p0007 p0015 p0021
  have p0023 :=
    @g_wpporbit0 (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) dv_cache_0001
  have p0024 :=
    Nominal.mp p0022 p0023
  exact p0024

noncomputable def g_elwppcand
    (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf (syn_wb (.classMem D (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C)) (.classMem D (syn_cwppreach F C)))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand F C)))
  have p0001 :=
    @g_eleq2i (syn_cwppcand F C) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C)) D p0000
  have p0002 :=
    @g_elin D (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C)
  have p0003 :=
    @g_elin D (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0004 :=
    @g_eliniseg (syn_clec) C D
  have p0005 :=
    @g_anbi2i (.classMem D (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_wbr D (syn_clec) C) (.classMem D (syn_chwcards (syn_cvv))) p0004
  have p0006 :=
    @g_bitri (.classMem D (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (.classMem D (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C)) p0003 p0005
  have p0007 :=
    @g_anbi1i (.classMem D (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C)) (.classMem D (syn_cwppreach F C)) p0006
  have p0008 :=
    @g_bitri (.classMem D (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C))) (syn_wa (.classMem D (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (.classMem D (syn_cwppreach F C))) (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C)) (.classMem D (syn_cwppreach F C))) p0002 p0007
  have p0009 :=
    @g_bitri (.classMem D (syn_cwppcand F C)) (.classMem D (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C))) (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C)) (.classMem D (syn_cwppreach F C))) p0001 p0008
  exact p0009

noncomputable def g_hwcnwendv
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact (show Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (A).fv from (by exact dv_A_u)))))), (show Disjoint ((A).fv) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have p0000 :=
    @g_hwcnpair u A
  have p0001 :=
    @g_hwcnraw u A
  have p0002 :=
    @g_eqeltrrd (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A) p0000 p0001
  have p0003 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0004 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0005 :=
    @g_elhwcodes A (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001 p0003 p0004
  have p0006 :=
    @g_biimpi (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) p0005
  have p0007 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) p0002 p0006
  have p0008 :=
    @g_simpl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)
  have p0009 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0007 p0008
  exact p0009

noncomputable def g_hwbaseswev
    (r : Var) (d : Var) (dv_d_r : d ≠ r) :
    Nominal.NPrf (syn_wb (.classMem (.cv d) (syn_chwbases (syn_cvv))) (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d)))) := by
  let proofSupport : Finset Var := ({r} : Finset Var) ∪ ({d} : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_ne_r : u ≠ r := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_u : r ≠ u :=
    Ne.symm fresh_u_ne_r
  have fresh_u_ne_d : u ≠ d := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_u : d ≠ u :=
    Ne.symm fresh_u_ne_d
  have dv_cache_0001 : Disjoint ((syn_cvv)).fv ((Class.cv d)).fv := by
    exact (show Disjoint ((syn_cvv)).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((∅ : Finset Var)) (({d} : Finset Var)) from (by simp))))
  have dv_cache_0002 : u ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (.cv d))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_u, (Ne.symm dv_d_r), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_r, fresh_u_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint ((syn_cvv)).fv ((syn_cin (.cv r) (syn_cxp (.cv d) (.cv d)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint ((syn_cvv)).fv ((syn_cin (.cv r) (syn_cxp (.cv d) (.cv d)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show Disjoint ((∅ : Finset Var)) ((((Class.cv r)).fv) ∪ (((syn_cxp (.cv d) (.cv d))).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((∅ : Finset Var)) (((Class.cv r)).fv) from (by simp)), (show Disjoint ((∅ : Finset Var)) (((syn_cxp (.cv d) (.cv d))).fv) from (by simp))⟩))))
  have dv_cache_0008 : u ∉ ((syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_r, fresh_u_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((syn_chwcn (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((Wff.classEq (.cv d) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_d, fresh_u_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : r ∉ ((Wff.classMem (.cv d) (syn_chwbases (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_d_r), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elhwbases u (syn_cvv) (.cv d) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_biimpi (.classMem (.cv d) (syn_chwbases (syn_cvv))) (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))) p0000
  have p0002 :=
    @g_hwcnwendv u (syn_cvv) dv_cache_0002
  have p0003 :=
    @g_adantr (.classMem (.cv u) (syn_chwcn (syn_cvv))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))) p0002
  have p0004 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))
  have p0005 :=
    @g_eqcomd (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))) (.cv d) (syn_cfv (syn_c2nd) (.cv u)) p0004
  have p0006 :=
    @g_breq2d (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u)) (.cv d) (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) p0005
  have p0007 :=
    @g_mpbid (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (.cv d)) p0003 p0006
  have p0008 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0009 :=
    @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0010 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r) (syn_cfv (syn_c1st) (.cv u)) (.cv d) (syn_cwe) p0009
  have p0011 :=
    @g_spcev (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (.cv d)) r (syn_cfv (syn_c1st) (.cv u)) dv_cache_0004 dv_cache_0005 p0008 p0010
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (.cv d)) (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0007 p0011
  have p0013 :=
    @g_ex (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))) (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0012
  have p0014 :=
    @g_rexlimiv (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))) (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) u (syn_chwcn (syn_cvv)) dv_cache_0006 p0013
  have p0015 :=
    @g_syl (.classMem (.cv d) (syn_chwbases (syn_cvv))) (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0001 p0014
  have p0016 :=
    @g_id (syn_wbr (.cv r) (syn_cwe) (.cv d))
  have p0017 :=
    @g_ssid (.cv d)
  have p0018 :=
    @g_a1i (syn_wss (.cv d) (.cv d)) (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0017
  have p0019 :=
    @g_brex (.cv r) (.cv d) (syn_cwe)
  have p0020 :=
    @g_simpr (.classMem (.cv r) (syn_cvv)) (.classMem (.cv d) (syn_cvv))
  have p0021 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (.cv d) (syn_cvv))) (.classMem (.cv d) (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_werestrndv (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (.cv d) (.cv r) p0016 p0018 p0021
  have p0023 :=
    @g_ssv (.cv d)
  have p0024 :=
    @g_a1i (syn_wss (.cv d) (syn_cvv)) (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0023
  have p0025 :=
    @g_jca (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (syn_cwe) (.cv d)) (syn_wss (.cv d) (syn_cvv)) p0022 p0024
  have p0026 :=
    @g_vex r
  have p0027 :=
    @g_vex d
  have p0028 :=
    @g_vex d
  have p0029 :=
    @g_xpex (.cv d) (.cv d) p0027 p0028
  have p0030 :=
    @g_inex (.cv r) (syn_cxp (.cv d) (.cv d)) p0026 p0029
  have p0031 :=
    @g_vex d
  have p0032 :=
    @g_elhwcodes (syn_cvv) (.cv d) (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) dv_cache_0007 p0030 p0031
  have p0033 :=
    @g_biimpri (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcodes (syn_cvv))) (syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (syn_cwe) (.cv d)) (syn_wss (.cv d) (syn_cvv))) p0032
  have p0034 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (syn_cwe) (.cv d)) (syn_wss (.cv d) (syn_cvv))) (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcodes (syn_cvv))) p0025 p0033
  have p0035 :=
    @g_inss2 (.cv r) (syn_cxp (.cv d) (.cv d))
  have p0036 :=
    @g_vex r
  have p0037 :=
    @g_vex d
  have p0038 :=
    @g_vex d
  have p0039 :=
    @g_xpex (.cv d) (.cv d) p0037 p0038
  have p0040 :=
    @g_inex (.cv r) (syn_cxp (.cv d) (.cv d)) p0036 p0039
  have p0041 :=
    @g_vex d
  have p0042 :=
    @g_opfv1st (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d) p0040 p0041
  have p0043 :=
    @g_vex r
  have p0044 :=
    @g_vex d
  have p0045 :=
    @g_vex d
  have p0046 :=
    @g_xpex (.cv d) (.cv d) p0044 p0045
  have p0047 :=
    @g_inex (.cv r) (syn_cxp (.cv d) (.cv d)) p0043 p0046
  have p0048 :=
    @g_vex d
  have p0049 :=
    @g_opfv2nd (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d) p0047 p0048
  have p0050 :=
    @g_vex r
  have p0051 :=
    @g_vex d
  have p0052 :=
    @g_vex d
  have p0053 :=
    @g_xpex (.cv d) (.cv d) p0051 p0052
  have p0054 :=
    @g_inex (.cv r) (syn_cxp (.cv d) (.cv d)) p0050 p0053
  have p0055 :=
    @g_vex d
  have p0056 :=
    @g_opfv2nd (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d) p0054 p0055
  have p0057 :=
    @g_xpeq12i (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (.cv d) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (.cv d) p0049 p0056
  have p0058 :=
    @g_sseq12i (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))) (syn_cxp (.cv d) (.cv d)) p0042 p0057
  have p0059 :=
    @g_mpbir (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))) (syn_wss (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (syn_cxp (.cv d) (.cv d))) p0035 p0058
  have p0060 :=
    @g_a1i (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))) (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0059
  have p0061 :=
    @g_jca (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcodes (syn_cvv))) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))) p0034 p0060
  have p0062 :=
    @g_vex r
  have p0063 :=
    @g_vex d
  have p0064 :=
    @g_vex d
  have p0065 :=
    @g_xpex (.cv d) (.cv d) p0063 p0064
  have p0066 :=
    @g_inex (.cv r) (syn_cxp (.cv d) (.cv d)) p0062 p0065
  have p0067 :=
    @g_vex d
  have p0068 :=
    @g_opex (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d) p0066 p0067
  have p0069 :=
    @g_elhwcncl (syn_cvv) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
  have p0070 :=
    Nominal.mp p0068 p0069
  have p0071 :=
    @g_biimpri (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcn (syn_cvv))) (syn_wa (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcodes (syn_cvv))) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))))) p0070
  have p0072 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wa (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcodes (syn_cvv))) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))))) (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcn (syn_cvv))) p0061 p0071
  have p0073 :=
    @g_vex r
  have p0074 :=
    @g_vex d
  have p0075 :=
    @g_vex d
  have p0076 :=
    @g_xpex (.cv d) (.cv d) p0074 p0075
  have p0077 :=
    @g_inex (.cv r) (syn_cxp (.cv d) (.cv d)) p0073 p0076
  have p0078 :=
    @g_vex d
  have p0079 :=
    @g_opfv2nd (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d) p0077 p0078
  have p0080 :=
    @g_eqcomi (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (.cv d) p0079
  have p0081 :=
    @g_a1i (.classEq (.cv d) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))) (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0080
  have p0082 :=
    @g_jca (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcn (syn_cvv))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))) p0072 p0081
  have p0083 :=
    @g_id (.classEq (.cv u) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
  have p0084 :=
    @g_fveq2d (.classEq (.cv u) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (.cv u) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_c2nd) p0083
  have p0085 :=
    @g_eqeq2d (.classEq (.cv u) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (.cv d) p0084
  have p0086 :=
    @g_rspcev (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))) u (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcn (syn_cvv)) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0085
  have p0087 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wa (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_chwcn (syn_cvv))) (.classEq (.cv d) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))) (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))) p0082 p0086
  have p0088 :=
    @g_elhwbases u (syn_cvv) (.cv d) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0089 :=
    @g_biimpri (.classMem (.cv d) (syn_chwbases (syn_cvv))) (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))) p0088
  have p0090 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv d) (syn_chwbases (syn_cvv))) p0087 p0089
  have p0091 :=
    @g_exlimiv (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classMem (.cv d) (syn_chwbases (syn_cvv))) r dv_cache_0011 p0090
  have p0092 :=
    @g_impbii (.classMem (.cv d) (syn_chwbases (syn_cvv))) (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0015 p0091
  exact p0092

noncomputable def g_elhwcardswev
    (k : Var) (s : Var) (d : Var) (dv_d_k : d ≠ k) (dv_d_s : d ≠ s) (dv_k_s : k ≠ s) :
    Nominal.NPrf (syn_wb (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))))) := by
  let proofSupport : Finset Var := ({k} : Finset Var) ∪ ({s} : Finset Var) ∪ ({d} : Finset Var)
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_k : r ≠ k := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_r : k ≠ r :=
    Ne.symm fresh_r_ne_k
  have fresh_r_ne_s : r ≠ s := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_r : s ≠ r :=
    Ne.symm fresh_r_ne_s
  have fresh_r_ne_d : r ≠ d := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_r : d ≠ r :=
    Ne.symm fresh_r_ne_d
  have dv_cache_0001 : Disjoint ((syn_cvv)).fv ((Class.cv k)).fv := by
    exact (show Disjoint ((syn_cvv)).fv ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((∅ : Finset Var)) (({k} : Finset Var)) from (by simp))))
  have dv_cache_0002 : r ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ s from (by exact fresh_r_ne_s))
  have dv_cache_0005 : s ∉ ((Wff.classEq (.cv k) (syn_cnc (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_s), fresh_s_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((Wff.classEq (.cv d) (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_d_s), fresh_s_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : d ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : d ∉ ((syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_s, fresh_d_ne_r, dv_d_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : r ∉ ((syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_s, fresh_r_ne_d, fresh_r_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : r ∉ ((syn_wbr (.cv s) (syn_cwe) (.cv d))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_s, fresh_r_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : d ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have dv_cache_0013 : r ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : r ∉ ((syn_chwbases (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : r ∉ ((Wff.classEq (.cv k) (syn_cnc (.cv d)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_k, fresh_r_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : d ∉ ((Wff.classMem (.cv k) (syn_chwcards (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : s ∉ ((Wff.classMem (.cv k) (syn_chwcards (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_s), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex k
  have p0001 :=
    @g_elhwcards (syn_cvv) (.cv k) r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r)))) p0001
  have p0003 :=
    @g_hwbaseswev s r dv_cache_0004
  have p0004 :=
    @g_biimpi (.classMem (.cv r) (syn_chwbases (syn_cvv))) (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r))) p0003
  have p0005 :=
    @g_adantr (.classMem (.cv r) (syn_chwbases (syn_cvv))) (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r))) (.classEq (.cv k) (syn_cnc (.cv r))) p0004
  have p0006 :=
    Nominal.ax1 (.classEq (.cv k) (syn_cnc (.cv r))) (syn_wbr (.cv s) (syn_cwe) (.cv r))
  have p0007 :=
    @g_alrimiv (.classEq (.cv k) (syn_cnc (.cv r))) (.imp (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))) s dv_cache_0005 p0006
  have p0008 :=
    @g_exintrbi (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r))) s
  have p0009 :=
    @g_syl (.classEq (.cv k) (syn_cnc (.cv r))) (.all s (.imp (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r))))) (syn_wb (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r))) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))))) p0007 p0008
  have p0010 :=
    @g_adantl (.classEq (.cv k) (syn_cnc (.cv r))) (syn_wb (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r))) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))))) (.classMem (.cv r) (syn_chwbases (syn_cvv))) p0009
  have p0011 :=
    @g_mpbid (syn_wa (.classMem (.cv r) (syn_chwbases (syn_cvv))) (.classEq (.cv k) (syn_cnc (.cv r)))) (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r))) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r))))) p0005 p0010
  have p0012 :=
    @g_vex r
  have p0013 :=
    @g_id (.classEq (.cv d) (.cv r))
  have p0014 :=
    @g_breq2d (.classEq (.cv d) (.cv r)) (.cv d) (.cv r) (.cv s) (syn_cwe) p0013
  have p0015 :=
    @g_id (.classEq (.cv d) (.cv r))
  have p0016 :=
    @g_nceqd (.classEq (.cv d) (.cv r)) (.cv d) (.cv r) p0015
  have p0017 :=
    @g_eqeq2d (.classEq (.cv d) (.cv r)) (syn_cnc (.cv d)) (syn_cnc (.cv r)) (.cv k) p0016
  have p0018 :=
    @g_anbi12d (.classEq (.cv d) (.cv r)) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv d))) (.classEq (.cv k) (syn_cnc (.cv r))) p0014 p0017
  have p0019 :=
    @g_exbidv (.classEq (.cv d) (.cv r)) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))) s dv_cache_0006 p0018
  have p0020 :=
    @g_spcev (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r))))) d (.cv r) dv_cache_0007 dv_cache_0008 p0012 p0019
  have p0021 :=
    @g_syl (syn_wa (.classMem (.cv r) (syn_chwbases (syn_cvv))) (.classEq (.cv k) (syn_cnc (.cv r)))) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r))))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))) p0011 p0020
  have p0022 :=
    @g_ex (.classMem (.cv r) (syn_chwbases (syn_cvv))) (.classEq (.cv k) (syn_cnc (.cv r))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))) p0021
  have p0023 :=
    @g_rexlimiv (.classEq (.cv k) (syn_cnc (.cv r))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))) r (syn_chwbases (syn_cvv)) dv_cache_0009 p0022
  have p0024 :=
    @g_syl (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r)))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))) p0002 p0023
  have p0025 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))
  have p0026 :=
    @g_vex s
  have p0027 :=
    @g_id (.classEq (.cv r) (.cv s))
  have p0028 :=
    @g_breq1d (.classEq (.cv r) (.cv s)) (.cv r) (.cv s) (.cv d) (syn_cwe) p0027
  have p0029 :=
    @g_spcev (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (.cv d)) r (.cv s) dv_cache_0010 dv_cache_0011 p0026 p0028
  have p0030 :=
    @g_hwbaseswev r d dv_cache_0012
  have p0031 :=
    @g_biimpri (.classMem (.cv d) (syn_chwbases (syn_cvv))) (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0030
  have p0032 :=
    @g_syl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) (.classMem (.cv d) (syn_chwbases (syn_cvv))) p0029 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classMem (.cv d) (syn_chwbases (syn_cvv))) p0025 p0032
  have p0034 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))
  have p0035 :=
    @g_jca (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))) (.classMem (.cv d) (syn_chwbases (syn_cvv))) (.classEq (.cv k) (syn_cnc (.cv d))) p0033 p0034
  have p0036 :=
    @g_id (.classEq (.cv r) (.cv d))
  have p0037 :=
    @g_nceqd (.classEq (.cv r) (.cv d)) (.cv r) (.cv d) p0036
  have p0038 :=
    @g_eqeq2d (.classEq (.cv r) (.cv d)) (syn_cnc (.cv r)) (syn_cnc (.cv d)) (.cv k) p0037
  have p0039 :=
    @g_rspcev (.classEq (.cv k) (syn_cnc (.cv r))) (.classEq (.cv k) (syn_cnc (.cv d))) r (.cv d) (syn_chwbases (syn_cvv)) dv_cache_0013 dv_cache_0014 dv_cache_0015 p0038
  have p0040 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))) (syn_wa (.classMem (.cv d) (syn_chwbases (syn_cvv))) (.classEq (.cv k) (syn_cnc (.cv d)))) (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r)))) p0035 p0039
  have p0041 :=
    @g_vex k
  have p0042 :=
    @g_elhwcards (syn_cvv) (.cv k) r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0041
  have p0043 :=
    @g_biimpri (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r)))) p0042
  have p0044 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))) (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r)))) (.classMem (.cv k) (syn_chwcards (syn_cvv))) p0040 p0043
  have p0045 :=
    @g_exlimivv (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))) (.classMem (.cv k) (syn_chwcards (syn_cvv))) d s dv_cache_0016 dv_cache_0017 p0044
  have p0046 :=
    @g_impbii (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))) p0024 p0045
  exact p0046

#print axioms g_elhwcardswev

end NFChoice.DirectNominalPrf.WPPReplay
