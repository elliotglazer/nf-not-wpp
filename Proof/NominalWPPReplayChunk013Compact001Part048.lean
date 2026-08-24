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
import NominalWPPReplayChunk013Compact001Part047

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

noncomputable def g_tcdi
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_n_0ex
  have p0003 :=
    @g_complex (syn_c0) p0002
  have p0004 :=
    @g_xpsnen (.cv x) (syn_ccompl (syn_c0)) p0001 p0003
  have p0005 :=
    @g_snex (syn_ccompl (syn_c0))
  have p0006 :=
    @g_xpex (.cv x) (syn_csn (syn_ccompl (syn_c0))) p0001 p0005
  have p0007 :=
    @g_eqnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (.cv x) p0006
  have p0008 :=
    @g_mpbir (.classEq (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (.cv x))) (syn_wbr (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cen) (.cv x)) p0004 p0007
  have p0009 :=
    @g_eqeq2i (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (.cv x)) A p0008
  have p0010 :=
    @g_vex y
  have p0011 :=
    @g_n_0ex
  have p0012 :=
    @g_xpsnen (.cv y) (syn_c0) p0010 p0011
  have p0013 :=
    @g_snex (syn_c0)
  have p0014 :=
    @g_xpex (.cv y) (syn_csn (syn_c0)) p0010 p0013
  have p0015 :=
    @g_eqnc (syn_cxp (.cv y) (syn_csn (syn_c0))) (.cv y) p0014
  have p0016 :=
    @g_mpbir (.classEq (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cnc (.cv y))) (syn_wbr (syn_cxp (.cv y) (syn_csn (syn_c0))) (syn_cen) (.cv y)) p0012 p0015
  have p0017 :=
    @g_eqeq2i (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cnc (.cv y)) B p0016
  have p0018 :=
    @g_anbi12i (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (.classEq B (syn_cnc (.cv y))) p0009 p0017
  have p0019 :=
    @g_n_2exbii (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) x y p0018
  have p0020 :=
    @g_elncs x A dv_cache_0003
  have p0021 :=
    @g_elncs y B dv_cache_0004
  have p0022 :=
    @g_anbi12i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x)))) (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y)))) p0020 p0021
  have p0023 :=
    @g_n_3bitr4ri (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))))) (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x)))) (syn_wex y (.classEq B (syn_cnc (.cv y))))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))))) (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) p0000 p0019 p0022
  have p0024 :=
    @g_ncelncsi (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) p0006
  have p0025 :=
    @g_ncelncsi (syn_cxp (.cv y) (syn_csn (syn_c0))) p0014
  have p0026 :=
    @g_ncaddccl (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0027 :=
    @g_mp2an (.classMem (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cncs)) (.classMem (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cncs)) (.classMem (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cncs)) p0024 p0025 p0026
  have p0028 :=
    @g_tccl (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_tccl (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
  have p0031 :=
    Nominal.mp p0024 p0030
  have p0032 :=
    @g_tccl (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0033 :=
    Nominal.mp p0025 p0032
  have p0034 :=
    @g_ncaddccl (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0035 :=
    @g_mp2an (.classMem (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_cncs)) (.classMem (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cncs)) (.classMem (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cncs)) p0031 p0033 p0034
  have p0036 :=
    @g_ncid (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) p0006
  have p0037 :=
    @g_ncid (syn_cxp (.cv y) (syn_csn (syn_c0))) p0014
  have p0038 :=
    @g_necompl (syn_c0)
  have p0039 :=
    @g_xpnedisj (.cv x) (.cv y) (syn_ccompl (syn_c0)) (syn_c0) p0003 p0038
  have p0040 :=
    @g_eladdci (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))) (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0041 :=
    @g_mp3an (.classMem (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classMem (syn_cxp (.cv y) (syn_csn (syn_c0))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (.classEq (syn_cin (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_c0)) (.classMem (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) p0036 p0037 p0039 p0040
  have p0042 :=
    @g_pw1eltc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0043 :=
    @g_mp2an (.classMem (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cncs)) (.classMem (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (.classMem (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))) p0027 p0041 p0042
  have p0044 :=
    @g_pw1un (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))
  have p0045 :=
    @g_pw1eltc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
  have p0046 :=
    @g_mp2an (.classMem (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cncs)) (.classMem (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classMem (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))) p0024 p0036 p0045
  have p0047 :=
    @g_pw1eltc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))
  have p0048 :=
    @g_mp2an (.classMem (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cncs)) (.classMem (syn_cxp (.cv y) (syn_csn (syn_c0))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (.classMem (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) p0025 p0037 p0047
  have p0049 :=
    @g_pw1eq (syn_cin (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_c0)
  have p0050 :=
    Nominal.mp p0039 p0049
  have p0051 :=
    @g_pw1in (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))
  have p0052 :=
    @g_pw10
  have p0053 :=
    @g_n_3eqtr3i (syn_cpw1 (syn_cin (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cpw1 (syn_c0)) (syn_cin (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_c0) p0050 p0051 p0052
  have p0054 :=
    @g_eladdci (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0055 :=
    @g_mp3an (.classMem (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))) (.classMem (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (.classEq (syn_cin (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_c0)) (.classMem (syn_cun (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))) p0046 p0048 p0053 p0054
  have p0056 :=
    @g_eqeltri (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cun (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) p0044 p0055
  have p0057 :=
    @g_nceleq (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0058 :=
    @g_mp4an (.classMem (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cncs)) (.classMem (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cncs)) (.classMem (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))) (.classMem (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))) (.classEq (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))) p0029 p0035 p0043 p0056 p0057
  have p0059 :=
    @g_addceq12 A B (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0060 :=
    @g_tceq (syn_cplc A B) (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0061 :=
    @g_syl (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (.classEq (syn_cplc A B) (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (.classEq (syn_ctc (syn_cplc A B)) (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))) p0059 p0060
  have p0062 :=
    @g_tceq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
  have p0063 :=
    @g_adantr (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq (syn_ctc A) (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) p0062
  have p0064 :=
    @g_tceq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0065 :=
    @g_adantl (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (.classEq (syn_ctc B) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) p0064
  have p0066 :=
    @g_addceq12d (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_ctc A) (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc B) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) p0063 p0065
  have p0067 :=
    @g_n_3eqtr4a (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B)) p0058 p0061 p0066
  have p0068 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B))) x y dv_cache_0005 dv_cache_0006 p0067
  have p0069 :=
    @g_sylbi (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))))) (.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B))) p0023 p0068
  exact p0069

noncomputable def g_tc1c
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cnc
  have p0001 :=
    @g_tccl (syn_c1c)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_n_1cnc
  have p0004 :=
    @g_n_0ex
  have p0005 :=
    @g_pw1sn (syn_c0) p0004
  have p0006 :=
    @g_n_1cnc
  have p0007 :=
    @g_n_0ex
  have p0008 :=
    @g_snel1c (syn_c0) p0007
  have p0009 :=
    @g_pw1eltc (syn_c1c) (syn_csn (syn_c0))
  have p0010 :=
    @g_mp2an (.classMem (syn_c1c) (syn_cncs)) (.classMem (syn_csn (syn_c0)) (syn_c1c)) (.classMem (syn_cpw1 (syn_csn (syn_c0))) (syn_ctc (syn_c1c))) p0006 p0008 p0009
  have p0011 :=
    @g_eqeltrri (syn_cpw1 (syn_csn (syn_c0))) (syn_csn (syn_csn (syn_c0))) (syn_ctc (syn_c1c)) p0005 p0010
  have p0012 :=
    @g_snex (syn_c0)
  have p0013 :=
    @g_snel1c (syn_csn (syn_c0)) p0012
  have p0014 :=
    @g_nceleq (syn_ctc (syn_c1c)) (syn_c1c) (syn_csn (syn_csn (syn_c0)))
  have p0015 :=
    @g_mp4an (.classMem (syn_ctc (syn_c1c)) (syn_cncs)) (.classMem (syn_c1c) (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_c0))) (syn_ctc (syn_c1c))) (.classMem (syn_csn (syn_csn (syn_c0))) (syn_c1c)) (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) p0002 p0003 p0011 p0013 p0014
  exact p0015

noncomputable def g_n_2nnc
     :
    Nominal.NPrf (.classMem (syn_c2c) (syn_cnnc)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1p1e2c
  have p0001 :=
    @g_n_1cnnc
  have p0002 :=
    @g_peano2 (syn_c1c)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_eqeltrri (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c) (syn_cnnc) p0000 p0003
  exact p0004

noncomputable def g_pw1fin
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cfin)) (.classMem (syn_cpw1 A) (syn_cfin))) := by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have dv_cache_0001 : m ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_wrex m (syn_cnnc) (syn_wa (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_A, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : m ∉ ((syn_cpw1 A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ncfinraise A A m (.cv n) dv_cache_0001 dv_cache_0001
  have p0001 :=
    @g_n_3anidm23 (.classMem (.cv n) (syn_cnnc)) (.classMem A (.cv n)) (syn_wrex m (syn_cnnc) (syn_wa (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m)))) p0000
  have p0002 :=
    @g_rexlimiva (.classMem A (.cv n)) (syn_wrex m (syn_cnnc) (syn_wa (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m)))) n (syn_cnnc) dv_cache_0002 p0001
  have p0003 :=
    @g_simpl (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m))
  have p0004 :=
    @g_reximi (syn_wa (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m))) (.classMem (syn_cpw1 A) (.cv m)) m (syn_cnnc) p0003
  have p0005 :=
    @g_syl (syn_wrex n (syn_cnnc) (.classMem A (.cv n))) (syn_wrex m (syn_cnnc) (syn_wa (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m)))) (syn_wrex m (syn_cnnc) (.classMem (syn_cpw1 A) (.cv m))) p0002 p0004
  have p0006 :=
    @g_elfin n A dv_cache_0003
  have p0007 :=
    @g_elfin m (syn_cpw1 A) dv_cache_0004
  have p0008 :=
    @g_n_3imtr4i (syn_wrex n (syn_cnnc) (.classMem A (.cv n))) (syn_wrex m (syn_cnnc) (.classMem (syn_cpw1 A) (.cv m))) (.classMem A (syn_cfin)) (.classMem (syn_cpw1 A) (syn_cfin)) p0005 p0006 p0007
  exact p0008

noncomputable def g_nntccl
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (.classMem (syn_ctc A) (syn_cnnc))) := by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (h)
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_ne_a : n ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_n : a ≠ n :=
    Ne.symm fresh_n_ne_a
  have fresh_m_ne_a : m ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_m : a ≠ m :=
    Ne.symm fresh_m_ne_a
  have dv_cache_0001 : n ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((Wff.classMem (.cv n) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : m ∉ ((syn_cpw1 (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : m ∉ ((Wff.classMem (syn_ctc A) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_A, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((Wff.classMem (syn_ctc A) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ ((Wff.classMem A (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nulnnn
  have p0001 :=
    @g_eleq1 A (syn_c0) (syn_cnnc)
  have p0002 :=
    @g_mtbiri (.classEq A (syn_c0)) (.classMem A (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc)) p0000 p0001
  have p0003 :=
    @g_necon2ai (.classMem A (syn_cnnc)) A (syn_c0) p0002
  have p0004 :=
    @g_n0 n A dv_cache_0001
  have p0005 :=
    @g_sylib (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)) (syn_wex n (.classMem (.cv n) A)) p0003 p0004
  have p0006 :=
    @g_eleq2 (.cv a) A (.cv n)
  have p0007_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv a) A) (syn_wb (.objMem n a) (.classMem (.cv n) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0006
  have p0007 :=
    @g_rspcev (.objMem n a) (.classMem (.cv n) A) a A (syn_cnnc) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0007_e00_recanon
  have p0008 :=
    @g_elfin a (.cv n) dv_cache_0005
  have p0009_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv n) (syn_cfin)) (syn_wrex a (syn_cnnc) (.objMem n a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint syn_wrex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0008
  have p0009 :=
    @g_sylibr (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A)) (syn_wrex a (syn_cnnc) (.objMem n a)) (.classMem (.cv n) (syn_cfin)) p0007 p0009_e01_recanon
  have p0010 :=
    @g_pw1fin (.cv n)
  have p0011 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A)) (.classMem (.cv n) (syn_cfin)) (.classMem (syn_cpw1 (.cv n)) (syn_cfin)) p0009 p0010
  have p0012 :=
    @g_elfin m (syn_cpw1 (.cv n)) dv_cache_0006
  have p0013 :=
    @g_sylib (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A)) (.classMem (syn_cpw1 (.cv n)) (syn_cfin)) (syn_wrex m (syn_cnnc) (.classMem (syn_cpw1 (.cv n)) (.cv m))) p0011 p0012
  have p0014 :=
    @g_nnnc A
  have p0015 :=
    @g_tccl A
  have p0016 :=
    @g_syl (.classMem A (syn_cnnc)) (.classMem A (syn_cncs)) (.classMem (syn_ctc A) (syn_cncs)) p0014 p0015
  have p0017 :=
    @g_ad2antrr (.classMem A (syn_cnnc)) (.classMem (syn_ctc A) (syn_cncs)) (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))) p0016
  have p0018 :=
    @g_nnnc (.cv m)
  have p0019 :=
    @g_ad2antlr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cncs)) (.classMem A (syn_cnnc)) (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))) p0018
  have p0020 :=
    @g_ad2antrr (.classMem A (syn_cnnc)) (.classMem A (syn_cncs)) (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))) p0014
  have p0021 :=
    @g_simprl (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))) (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))
  have p0022 :=
    @g_pw1eltc A (.cv n)
  have p0023 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))) (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m)))) (.classMem A (syn_cncs)) (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (syn_ctc A)) p0020 p0021 p0022
  have p0024 :=
    @g_simprr (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))) (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))
  have p0025 :=
    @g_nceleq (syn_ctc A) (.cv m) (syn_cpw1 (.cv n))
  have p0026 :=
    @g_syl22anc (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))) (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m)))) (.classMem (syn_ctc A) (syn_cncs)) (.classMem (.cv m) (syn_cncs)) (.classMem (syn_cpw1 (.cv n)) (syn_ctc A)) (.classMem (syn_cpw1 (.cv n)) (.cv m)) (.classEq (syn_ctc A) (.cv m)) p0017 p0019 p0023 p0024 p0025
  have p0027 :=
    @g_simplr (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m)))
  have p0028 :=
    @g_eqeltrd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))) (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m)))) (syn_ctc A) (.cv m) (syn_cnnc) p0026 p0027
  have p0029 :=
    @g_expr (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))) (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m)) (.classMem (syn_ctc A) (syn_cnnc)) p0028
  have p0030 :=
    @g_an32s (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) A) (.imp (.classMem (syn_cpw1 (.cv n)) (.cv m)) (.classMem (syn_ctc A) (syn_cnnc))) p0029
  have p0031 :=
    @g_rexlimdva (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A)) (.classMem (syn_cpw1 (.cv n)) (.cv m)) (.classMem (syn_ctc A) (syn_cnnc)) m (syn_cnnc) dv_cache_0007 dv_cache_0008 p0030
  have p0032 :=
    @g_mpd (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A)) (syn_wrex m (syn_cnnc) (.classMem (syn_cpw1 (.cv n)) (.cv m))) (.classMem (syn_ctc A) (syn_cnnc)) p0013 p0031
  have p0033 :=
    @g_ex (.classMem A (syn_cnnc)) (.classMem (.cv n) A) (.classMem (syn_ctc A) (syn_cnnc)) p0032
  have p0034 :=
    @g_exlimdv (.classMem A (syn_cnnc)) (.classMem (.cv n) A) (.classMem (syn_ctc A) (syn_cnnc)) n dv_cache_0009 dv_cache_0010 p0033
  have p0035 :=
    @g_mpd (.classMem A (syn_cnnc)) (syn_wex n (.classMem (.cv n) A)) (.classMem (syn_ctc A) (syn_cnnc)) p0005 p0034
  exact p0035

noncomputable def g_nclec
    (A : Class) (B : Class) (hyp_nclec_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_nclec_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wss A (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wss A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_ncid A hyp_nclec_1
  have p0001 :=
    @g_ncid B hyp_nclec_2
  have p0002 :=
    @g_sseq1 (.cv x) A (.cv y)
  have p0003 :=
    @g_sseq2 (.cv y) B A
  have p0004 :=
    @g_rspc2ev (syn_wss (.cv x) (.cv y)) (syn_wss A B) (syn_wss A (.cv y)) x y A B (syn_cnc A) (syn_cnc B) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0002 p0003
  have p0005 :=
    @g_mp3an12 (.classMem A (syn_cnc A)) (.classMem B (syn_cnc B)) (syn_wss A B) (syn_wrex x (syn_cnc A) (syn_wrex y (syn_cnc B) (syn_wss (.cv x) (.cv y)))) p0000 p0001 p0004
  have p0006 :=
    @g_ncex A
  have p0007 :=
    @g_ncex B
  have p0008 :=
    @g_brlec x y (syn_cnc A) (syn_cnc B) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0009 p0006 p0007
  have p0009 :=
    @g_sylibr (syn_wss A B) (syn_wrex x (syn_cnc A) (syn_wrex y (syn_cnc B) (syn_wss (.cv x) (.cv y)))) (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) p0005 p0008
  exact p0009

noncomputable def g_lecidg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (syn_wne A (syn_c0))) (syn_wbr A (syn_clec) A)) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_wss (.cv x) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_ssid (.cv x)
  have p0001 :=
    @g_sseq2 (.cv y) (.cv x) (.cv x)
  have p0002 :=
    @g_rspcev (syn_wss (.cv x) (.cv y)) (syn_wss (.cv x) (.cv x)) y (.cv x) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @g_mpan2 (.classMem (.cv x) A) (syn_wss (.cv x) (.cv x)) (syn_wrex y A (syn_wss (.cv x) (.cv y))) p0000 p0002
  have p0004 :=
    @g_ancli (.classMem (.cv x) A) (syn_wrex y A (syn_wss (.cv x) (.cv y))) p0003
  have p0005 :=
    @g_eximi (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (syn_wrex y A (syn_wss (.cv x) (.cv y)))) x p0004
  have p0006 :=
    @g_n0 x A dv_cache_0004
  have p0007 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y))))))
  have p0008 :=
    @g_n_3imtr4i (syn_wex x (.classMem (.cv x) A)) (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wrex y A (syn_wss (.cv x) (.cv y))))) (syn_wne A (syn_c0)) (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y)))) p0005 p0006 p0007
  have p0009 :=
    @g_adantl (syn_wne A (syn_c0)) (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y)))) (.classMem A V) p0008
  have p0010 :=
    @g_brlecg x y A A V V dv_cache_0004 dv_cache_0004 dv_cache_0002 dv_cache_0005
  have p0011 :=
    @g_anidms (.classMem A V) (syn_wb (syn_wbr A (syn_clec) A) (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y))))) p0010
  have p0012 :=
    @g_adantr (.classMem A V) (syn_wb (syn_wbr A (syn_clec) A) (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y))))) (syn_wne A (syn_c0)) p0011
  have p0013 :=
    @g_mpbird (syn_wa (.classMem A V) (syn_wne A (syn_c0))) (syn_wbr A (syn_clec) A) (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y)))) p0009 p0012
  exact p0013

noncomputable def g_nclecid
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cncs)) (syn_wbr A (syn_clec) A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_nulnnc
  have p0001 :=
    @g_eleq1 A (syn_c0) (syn_cncs)
  have p0002 :=
    @g_mtbiri (.classEq A (syn_c0)) (.classMem A (syn_cncs)) (.classMem (syn_c0) (syn_cncs)) p0000 p0001
  have p0003 :=
    @g_necon2ai (.classMem A (syn_cncs)) A (syn_c0) p0002
  have p0004 :=
    @g_lecidg A (syn_cncs)
  have p0005 :=
    @g_mpdan (.classMem A (syn_cncs)) (syn_wne A (syn_c0)) (syn_wbr A (syn_clec) A) p0003 p0004
  exact p0005

#print axioms g_nclecid

end NFChoice.DirectNominalPrf.WPPReplay
