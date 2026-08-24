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
import NominalWPPReplayChunk016Compact001Part058

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

noncomputable def g_hwnisolnkereqndv
    (A : Class) (hyp_hwnisolnkereqndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_clnker (syn_chwniso A)) (syn_chwniso A)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_clnker (syn_chwniso A))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_clnker (syn_chwniso A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_brlnker (syn_chwniso A) (.cv x) (.cv y)
  have p0001 :=
    @g_simpl (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr (.cv y) (syn_chwniso A) (.cv x))
  have p0002 :=
    @g_id (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
  have p0003 :=
    @g_hwnisoerv A
  have p0004 :=
    Nominal.mp hyp_hwnisolnkereqndv_1 p0003
  have p0005 :=
    @g_a1i (syn_wbr (syn_chwniso A) (syn_cer) (syn_cvv)) (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) p0004
  have p0006 :=
    @g_brreldmex (.cv x) (.cv y) (syn_chwniso A)
  have p0007 :=
    @g_brrelrnex (.cv x) (.cv y) (syn_chwniso A)
  have p0008 :=
    @g_id (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
  have p0009 :=
    @g_ersym (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_cvv) (syn_chwniso A) (.cv x) (.cv y) p0005 p0006 p0007 p0008
  have p0010 :=
    @g_jca (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr (.cv y) (syn_chwniso A) (.cv x)) p0002 p0009
  have p0011 :=
    @g_impbii (syn_wa (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr (.cv y) (syn_chwniso A) (.cv x))) (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) p0001 p0010
  have p0012 :=
    @g_bitri (syn_wbr (.cv x) (syn_clnker (syn_chwniso A)) (.cv y)) (syn_wa (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr (.cv y) (syn_chwniso A) (.cv x))) (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) p0000 p0011
  have p0013 :=
    @g_eqbrriv x y (syn_clnker (syn_chwniso A)) (syn_chwniso A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0012
  exact p0013

noncomputable def g_lnpwhnordvalndv
    (A : Class) (hyp_lnpwhnordvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A)))) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hwnisoex A hyp_lnpwhnordvalndv_1
  have p0001 :=
    @g_hwcnex A hyp_lnpwhnordvalndv_1
  have p0002 :=
    @g_lnpwquofnval (syn_chwcn A) (syn_chwniso A) p0000 p0001
  have p0003 :=
    @g_hwnisolnkereqndv A hyp_lnpwhnordvalndv_1
  have p0004 :=
    @g_qseq2 (syn_clnker (syn_chwniso A)) (syn_chwniso A) (syn_chwcn A)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0007 :=
    @g_eqcomi (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0006
  have p0008 :=
    @g_eqtri (syn_cqs (syn_chwcn A) (syn_clnker (syn_chwniso A))) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A) p0005 p0007
  have p0009 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A)))) (syn_cqs (syn_chwcn A) (syn_clnker (syn_chwniso A))) (syn_chnord A) p0002 p0008
  exact p0009

noncomputable def g_wpplitphnordpointfnexndv
     :
    Nominal.NPrf (.classMem (syn_cwpplitphnordpointfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwpplitphnordpointfn] using (Nominal.classEqRefl (syn_cwpplitphnordpointfn)))
  have p0001 :=
    @g_lnpwquofnex
  have p0002 :=
    @g_wpphninputfnexndv
  have p0003 :=
    @g_coex (syn_clnpwquofn) (syn_cwpphninputfn) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cwpplitphnordpointfn) (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_wpplitphnordpointfnfnndv
     :
    Nominal.NPrf (syn_wfn (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_lnpwquofnfn
  have p0001 :=
    @g_wpphninputfnmapndv
  have p0002 :=
    @g_ffn (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_cwpphninputfn)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_dffn2 (syn_cpw1 (syn_cvv)) (syn_cwpphninputfn)
  have p0005 :=
    @g_mpbi (syn_wfn (syn_cwpphninputfn) (syn_cpw1 (syn_cvv))) (syn_wf (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_clnpwquofn) (syn_cvv)) (syn_wf (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)) (syn_cvv)) p0000 p0005
  have p0007 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cvv)) (syn_clnpwquofn) (syn_cwpphninputfn)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    (by simpa [syn_cwpplitphnordpointfn] using (Nominal.classEqRefl (syn_cwpplitphnordpointfn)))
  have p0010 :=
    @g_fneq1i (syn_cpw1 (syn_cvv)) (syn_cwpplitphnordpointfn) (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) p0009
  have p0011 :=
    @g_mpbir (syn_wfn (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cvv))) (syn_wfn (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) (syn_cpw1 (syn_cvv))) p0008 p0010
  exact p0011

noncomputable def g_wpplitphnordpointfnvalndv
    (A : Class) (hyp_wpplitphnordpointfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn A))) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cwpplitphnordpointfn] using (Nominal.classEqRefl (syn_cwpplitphnordpointfn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn A)) (syn_cwpplitphnordpointfn) (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) p0000
  have p0002 :=
    @g_wpphninputfnmapndv
  have p0003 :=
    @g_ffn (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_cwpphninputfn)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_snex A
  have p0006 :=
    @g_snelpw1 (syn_csn A) (syn_cvv)
  have p0007 :=
    @g_mpbir (.classMem (syn_csn (syn_csn A)) (syn_cpw1 (syn_cvv))) (.classMem (syn_csn A) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_cwpphninputfn) (syn_cpw1 (syn_cvv))) (.classMem (syn_csn (syn_csn A)) (syn_cpw1 (syn_cvv))) p0004 p0007
  have p0009 :=
    @g_fvco2 (syn_cpw1 (syn_cvv)) (syn_csn (syn_csn A)) (syn_clnpwquofn) (syn_cwpphninputfn)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_wpphninputfnvalndv A hyp_wpplitphnordpointfnvalndv_1
  have p0012 :=
    @g_fveq2i (syn_cfv (syn_cwpphninputfn) (syn_csn (syn_csn A))) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A))) (syn_clnpwquofn) p0011
  have p0013 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) (syn_csn (syn_csn A))) (syn_cfv (syn_clnpwquofn) (syn_cfv (syn_cwpphninputfn) (syn_csn (syn_csn A)))) (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A)))) p0010 p0012
  have p0014 :=
    @g_lnpwhnordvalndv A hyp_wpplitphnordpointfnvalndv_1
  have p0015 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) (syn_csn (syn_csn A))) (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A)))) (syn_chnord A) p0013 p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn A))) (syn_cfv (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) (syn_csn (syn_csn A))) (syn_chnord A) p0001 p0015
  exact p0016

noncomputable def g_hncardnceqsetimpndv
    (D : Class) (E : Class) :
    Nominal.NPrf (.imp (.classMem D (syn_cvv)) (.imp (.classEq (syn_cnc D) (syn_cnc E)) (.classEq (syn_chncard D) (syn_chncard E)))) := by
  let proofSupport : Finset Var := D.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ (E).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.classEq (syn_chncard D) (syn_chncard E))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqncg D E (syn_cvv)
  have p0001 :=
    @g_biimpd (.classMem D (syn_cvv)) (.classEq (syn_cnc D) (syn_cnc E)) (syn_wbr D (syn_cen) E) p0000
  have p0002 :=
    @g_bren D E f dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_biimpi (syn_wbr D (syn_cen) E) (syn_wex f (syn_wf1o (.cv f) D E)) p0002
  have p0004 :=
    @g_syl6 (.classMem D (syn_cvv)) (.classEq (syn_cnc D) (syn_cnc E)) (syn_wbr D (syn_cen) E) (syn_wex f (syn_wf1o (.cv f) D E)) p0001 p0003
  have p0005 :=
    @g_vex f
  have p0006 :=
    @g_hncardf1oimpndv D E (.cv f) p0005
  have p0007 :=
    @g_exlimiv (syn_wf1o (.cv f) D E) (.classEq (syn_chncard D) (syn_chncard E)) f dv_cache_0003 p0006
  have p0008 :=
    @g_syl6 (.classMem D (syn_cvv)) (.classEq (syn_cnc D) (syn_cnc E)) (syn_wex f (syn_wf1o (.cv f) D E)) (.classEq (syn_chncard D) (syn_chncard E)) p0004 p0007
  exact p0008

noncomputable def g_hnordncmemimpndv
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_cnc A)) (.classMem (syn_chnord B) (syn_cnc (syn_chnord A)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_elex B (syn_cnc A)
  have p0001 :=
    @g_hnordexg B
  have p0002 :=
    @g_syl (.classMem B (syn_cnc A)) (.classMem B (syn_cvv)) (.classMem (syn_chnord B) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_ncidg (syn_chnord B) (syn_cvv)
  have p0004 :=
    @g_syl (.classMem B (syn_cnc A)) (.classMem (syn_chnord B) (syn_cvv)) (.classMem (syn_chnord B) (syn_cnc (syn_chnord B))) p0002 p0003
  have p0005 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard B)))
  have p0006 :=
    @g_eqcomi (syn_chncard B) (syn_cnc (syn_chnord B)) p0005
  have p0007 :=
    @g_a1i (.classEq (syn_cnc (syn_chnord B)) (syn_chncard B)) (.classMem B (syn_cnc A)) p0006
  have p0008 :=
    @g_elnc B A
  have p0009 :=
    @g_biimpi (.classMem B (syn_cnc A)) (syn_wbr B (syn_cen) A) p0008
  have p0010 :=
    @g_elex B (syn_cnc A)
  have p0011 :=
    @g_eqncg B A (syn_cvv)
  have p0012 :=
    @g_syl (.classMem B (syn_cnc A)) (.classMem B (syn_cvv)) (syn_wb (.classEq (syn_cnc B) (syn_cnc A)) (syn_wbr B (syn_cen) A)) p0010 p0011
  have p0013 :=
    @g_mpbird (.classMem B (syn_cnc A)) (.classEq (syn_cnc B) (syn_cnc A)) (syn_wbr B (syn_cen) A) p0009 p0012
  have p0014 :=
    @g_elex B (syn_cnc A)
  have p0015 :=
    @g_hncardnceqsetimpndv B A
  have p0016 :=
    @g_syl (.classMem B (syn_cnc A)) (.classMem B (syn_cvv)) (.imp (.classEq (syn_cnc B) (syn_cnc A)) (.classEq (syn_chncard B) (syn_chncard A))) p0014 p0015
  have p0017 :=
    @g_mpd (.classMem B (syn_cnc A)) (.classEq (syn_cnc B) (syn_cnc A)) (.classEq (syn_chncard B) (syn_chncard A)) p0013 p0016
  have p0018 :=
    @g_eqtrd (.classMem B (syn_cnc A)) (syn_cnc (syn_chnord B)) (syn_chncard B) (syn_chncard A) p0007 p0017
  have p0019 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard A)))
  have p0020 :=
    @g_a1i (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))) (.classMem B (syn_cnc A)) p0019
  have p0021 :=
    @g_eqtrd (.classMem B (syn_cnc A)) (syn_cnc (syn_chnord B)) (syn_chncard A) (syn_cnc (syn_chnord A)) p0018 p0020
  have p0022 :=
    @g_eleqtrd (.classMem B (syn_cnc A)) (syn_chnord B) (syn_cnc (syn_chnord B)) (syn_cnc (syn_chnord A)) p0004 p0021
  exact p0022

noncomputable def g_enimasatndv
    (A : Class) (Q : Class) (hyp_enimasatndv_1 : Nominal.NPrf (.classMem A Q)) (hyp_enimasatndv_2 : Nominal.NPrf (syn_wss Q (syn_cnc A))) :
    Nominal.NPrf (.classEq (syn_cima (syn_cen) Q) (syn_cnc A)) := by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_Q : x ∉ Q.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_Q : y ∉ Q.fv := by
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
  have dv_cache_0002 : y ∉ ((syn_cen)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (Q).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classMem (.cv x) (syn_cnc A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cima (syn_cen) Q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elima y (.cv x) (syn_cen) Q dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_biimpi (.classMem (.cv x) (syn_cima (syn_cen) Q)) (syn_wrex y Q (syn_wbr (.cv y) (syn_cen) (.cv x))) p0000
  have p0002 :=
    @g_simpr (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))
  have p0003 :=
    @g_ensymi (.cv y) (.cv x)
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))) (syn_wbr (.cv y) (syn_cen) (.cv x)) (syn_wbr (.cv x) (syn_cen) (.cv y)) p0002 p0003
  have p0005 :=
    @g_simpl (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))
  have p0006 :=
    @g_sseli Q (syn_cnc A) (.cv y) hyp_enimasatndv_2
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))) (.classMem (.cv y) Q) (.classMem (.cv y) (syn_cnc A)) p0005 p0006
  have p0008 :=
    @g_elnc (.cv y) A
  have p0009 :=
    @g_sylib (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))) (.classMem (.cv y) (syn_cnc A)) (syn_wbr (.cv y) (syn_cen) A) p0007 p0008
  have p0010 :=
    @g_jca (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))) (syn_wbr (.cv x) (syn_cen) (.cv y)) (syn_wbr (.cv y) (syn_cen) A) p0004 p0009
  have p0011 :=
    @g_entr (.cv x) (.cv y) A
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))) (syn_wa (syn_wbr (.cv x) (syn_cen) (.cv y)) (syn_wbr (.cv y) (syn_cen) A)) (syn_wbr (.cv x) (syn_cen) A) p0010 p0011
  have p0013 :=
    @g_elnc (.cv x) A
  have p0014 :=
    @g_sylibr (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))) (syn_wbr (.cv x) (syn_cen) A) (.classMem (.cv x) (syn_cnc A)) p0012 p0013
  have p0015 :=
    @g_rexlimiva (syn_wbr (.cv y) (syn_cen) (.cv x)) (.classMem (.cv x) (syn_cnc A)) y Q dv_cache_0004 p0014
  have p0016 :=
    @g_syl (.classMem (.cv x) (syn_cima (syn_cen) Q)) (syn_wrex y Q (syn_wbr (.cv y) (syn_cen) (.cv x))) (.classMem (.cv x) (syn_cnc A)) p0001 p0015
  have p0017 :=
    @g_ssriv x (syn_cima (syn_cen) Q) (syn_cnc A) dv_cache_0005 dv_cache_0006 p0016
  have p0018 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc A)))
  have p0019 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec A (syn_cen))))
  have p0020 :=
    @g_eqtri (syn_cnc A) (syn_cec A (syn_cen)) (syn_cima (syn_cen) (syn_csn A)) p0018 p0019
  have p0021 :=
    @g_snssi A Q
  have p0022 :=
    Nominal.mp hyp_enimasatndv_1 p0021
  have p0023 :=
    @g_imass2 (syn_csn A) Q (syn_cen)
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_eqsstri (syn_cnc A) (syn_cima (syn_cen) (syn_csn A)) (syn_cima (syn_cen) Q) p0020 p0024
  have p0026 :=
    @g_eqssi (syn_cima (syn_cen) Q) (syn_cnc A) p0017 p0025
  exact p0026

noncomputable def g_wpplitphnordpointfnvalimpndv
    (q : Var) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv q)) (syn_chnord (syn_cuni (syn_cuni (.cv q)))))) := by
  let proofSupport : Finset Var := ({q} : Finset Var)
  have dv_cache_0001 : q ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdcolcodearg (syn_cvv) q dv_cache_0001
  have p0001 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv)) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0002 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv)) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0000 p0001
  have p0003 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cwpplitphnordpointfn) p0002
  have p0004 :=
    @g_vex q
  have p0005 :=
    @g_uniex (.cv q) p0004
  have p0006 :=
    @g_uniex (syn_cuni (.cv q)) p0005
  have p0007 :=
    @g_wpplitphnordpointfnvalndv (syn_cuni (syn_cuni (.cv q))) p0006
  have p0008 :=
    @g_a1i (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_chnord (syn_cuni (syn_cuni (.cv q))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0007
  have p0009 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cfv (syn_cwpplitphnordpointfn) (.cv q)) (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_chnord (syn_cuni (syn_cuni (.cv q)))) p0003 p0008
  exact p0009

noncomputable def g_wpplitphnordimexndv
    (Q : Class) (hyp_wpplitphnordimexndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) (syn_cvv)) := by
  let proofSupport : Finset Var := Q.fv
  have p0000 :=
    @g_wpplitphnordpointfnexndv
  have p0001 :=
    @g_pw1ex Q hyp_wpplitphnordimexndv_1
  have p0002 :=
    @g_pw1ex (syn_cpw1 Q) p0001
  have p0003 :=
    @g_imaex (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)) p0000 p0002
  exact p0003

noncomputable def g_wpplitphnordimcanndv
    (C : Class) (Q : Class) (hyp_wpplitphnordimcanndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) (hyp_wpplitphnordimcanndv_2 : Nominal.NPrf (.classMem C Q)) :
    Nominal.NPrf (.classMem (syn_chnord C) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))) := by
  let proofSupport : Finset Var := C.fv ∪ Q.fv
  have p0000 :=
    @g_elexi C Q hyp_wpplitphnordimcanndv_2
  have p0001 :=
    @g_wpplitphnordpointfnvalndv C p0000
  have p0002 :=
    @g_eqcomi (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn C))) (syn_chnord C) p0001
  have p0003 :=
    @g_snelpw1 C Q
  have p0004 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 Q)) (.classMem C Q) hyp_wpplitphnordimcanndv_2 p0003
  have p0005 :=
    @g_snelpw1 (syn_csn C) (syn_cpw1 Q)
  have p0006 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cpw1 Q))) (.classMem (syn_csn C) (syn_cpw1 Q)) p0004 p0005
  have p0007 :=
    @g_wpplitphnordpointfnfnndv
  have p0008 :=
    @g_fnfun (syn_cpw1 (syn_cvv)) (syn_cwpplitphnordpointfn)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_snex C
  have p0011 :=
    @g_snelpw1 (syn_csn C) (syn_cvv)
  have p0012 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cvv))) (.classMem (syn_csn C) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_wpplitphnordpointfnfnndv
  have p0014 :=
    @g_fndm (syn_cpw1 (syn_cvv)) (syn_cwpplitphnordpointfn)
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_eleq2i (syn_cdm (syn_cwpplitphnordpointfn)) (syn_cpw1 (syn_cvv)) (syn_csn (syn_csn C)) p0015
  have p0017 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cdm (syn_cwpplitphnordpointfn))) (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cvv))) p0012 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfun (syn_cwpplitphnordpointfn)) (.classMem (syn_csn (syn_csn C)) (syn_cdm (syn_cwpplitphnordpointfn))) p0009 p0017
  have p0019 :=
    @g_funfvima (syn_cpw1 (syn_cpw1 Q)) (syn_csn (syn_csn C)) (syn_cwpplitphnordpointfn)
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    Nominal.mp p0006 p0020
  have p0022 :=
    @g_eqeltri (syn_chnord C) (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn C))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) p0002 p0021
  exact p0022

noncomputable def g_wpplitphnordimssndv
    (C : Class) (Q : Class) (hyp_wpplitphnordimssndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) (hyp_wpplitphnordimssndv_2 : Nominal.NPrf (syn_wss Q (syn_cnc C))) :
    Nominal.NPrf (syn_wss (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) (syn_cnc (syn_chnord C))) := by
  let proofSupport : Finset Var := C.fv ∪ Q.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_Q : y ∉ Q.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_Q : x ∉ Q.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((syn_cpw1 (syn_cpw1 Q))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cwpplitphnordpointfn)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (Q).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) (syn_cnc (syn_chnord C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cnc (syn_chnord C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wpplitphnordpointfnfnndv
  have p0001 :=
    @g_ssv (syn_cpw1 Q)
  have p0002 :=
    @g_pw1ss (syn_cpw1 Q) (syn_cvv)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cvv))) (syn_wss (syn_cpw1 (syn_cpw1 Q)) (syn_cpw1 (syn_cvv))) p0000 p0003
  have p0005 :=
    @g_fvelimab x (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cpw1 Q)) (.cv y) (syn_cwpplitphnordpointfn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_biimpi (.classMem (.cv y) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))) (syn_wrex x (syn_cpw1 (syn_cpw1 Q)) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) p0006
  have p0008 :=
    @g_simpr (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))
  have p0009 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))
  have p0010 :=
    @g_ssv Q
  have p0011 :=
    @g_pw1ss Q (syn_cvv)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_pw1ss (syn_cpw1 Q) (syn_cpw1 (syn_cvv))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_sseli (syn_cpw1 (syn_cpw1 Q)) (syn_cpw1 (syn_cpw1 (syn_cvv))) (.cv x) p0014
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classMem (.cv x) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0009 p0015
  have p0017 :=
    @g_wpplitphnordpointfnvalimpndv x
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) (.classMem (.cv x) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (syn_chnord (syn_cuni (syn_cuni (.cv x))))) p0016 p0017
  have p0019 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))
  have p0020 :=
    @g_fdcolcodearg Q x dv_cache_0004
  have p0021 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) Q) (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))) p0019 p0020
  have p0022 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv x))) Q) (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))
  have p0023 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) Q) (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))) (.classMem (syn_cuni (syn_cuni (.cv x))) Q) p0021 p0022
  have p0024 :=
    @g_sseli Q (syn_cnc C) (syn_cuni (syn_cuni (.cv x))) hyp_wpplitphnordimssndv_2
  have p0025 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) (.classMem (syn_cuni (syn_cuni (.cv x))) Q) (.classMem (syn_cuni (syn_cuni (.cv x))) (syn_cnc C)) p0023 p0024
  have p0026 :=
    @g_hnordncmemimpndv C (syn_cuni (syn_cuni (.cv x)))
  have p0027 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) (.classMem (syn_cuni (syn_cuni (.cv x))) (syn_cnc C)) (.classMem (syn_chnord (syn_cuni (syn_cuni (.cv x)))) (syn_cnc (syn_chnord C))) p0025 p0026
  have p0028 :=
    @g_eqeltrd (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (syn_chnord (syn_cuni (syn_cuni (.cv x)))) (syn_cnc (syn_chnord C)) p0018 p0027
  have p0029 :=
    @g_eqeltrrd (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y) (syn_cnc (syn_chnord C)) p0008 p0028
  have p0030 :=
    @g_rexlimiva (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)) (.classMem (.cv y) (syn_cnc (syn_chnord C))) x (syn_cpw1 (syn_cpw1 Q)) dv_cache_0005 p0029
  have p0031 :=
    @g_syl (.classMem (.cv y) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))) (syn_wrex x (syn_cpw1 (syn_cpw1 Q)) (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))) (.classMem (.cv y) (syn_cnc (syn_chnord C))) p0007 p0030
  have p0032 :=
    @g_ssriv y (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) (syn_cnc (syn_chnord C)) dv_cache_0006 dv_cache_0007 p0031
  exact p0032

noncomputable def g_wpplitphnordcardvalndv
    (C : Class) (Q : Class) (hyp_wpplitphnordcardvalndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) (hyp_wpplitphnordcardvalndv_2 : Nominal.NPrf (.classMem C Q)) (hyp_wpplitphnordcardvalndv_3 : Nominal.NPrf (syn_wss Q (syn_cnc C))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage (syn_cen)) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))) (syn_chncard C)) := by
  let proofSupport : Finset Var := C.fv ∪ Q.fv
  have p0000 :=
    @g_enex
  have p0001 :=
    @g_wpplitphnordimexndv Q hyp_wpplitphnordcardvalndv_1
  have p0002 :=
    @g_fvimagecl (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) (syn_cen) p0000 p0001
  have p0003 :=
    @g_wpplitphnordimcanndv C Q hyp_wpplitphnordcardvalndv_1 hyp_wpplitphnordcardvalndv_2
  have p0004 :=
    @g_wpplitphnordimssndv C Q hyp_wpplitphnordcardvalndv_1 hyp_wpplitphnordcardvalndv_3
  have p0005 :=
    @g_enimasatndv (syn_chnord C) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) p0003 p0004
  have p0006 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cen)) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))) (syn_cima (syn_cen) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))) (syn_cnc (syn_chnord C)) p0002 p0005
  have p0007 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard C)))
  have p0008 :=
    @g_eqcomi (syn_chncard C) (syn_cnc (syn_chnord C)) p0007
  have p0009 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cen)) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))) (syn_cnc (syn_chnord C)) (syn_chncard C) p0006 p0008
  exact p0009

noncomputable def g_wpppowset2fnexndv
     :
    Nominal.NPrf (.classMem (syn_cwpppowset2fn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwpppowset2fn] using (Nominal.classEqRefl (syn_cwpppowset2fn)))
  have p0001 :=
    @g_wpppowsetfnexndv
  have p0002 :=
    @g_wpppowsetfnexndv
  have p0003 :=
    @g_siex (syn_cwpppowsetfn) p0002
  have p0004 :=
    @g_coex (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn)) p0001 p0003
  have p0005 :=
    @g_eqeltri (syn_cwpppowset2fn) (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_cvv) p0000 p0004
  exact p0005

noncomputable def g_wpppowset2fnfnndv
     :
    Nominal.NPrf (syn_wfn (syn_cwpppowset2fn) (syn_cpw1 (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_wpppowsetfnfnndv
  have p0001 :=
    @g_wpppowsetfnfnndv
  have p0002 :=
    @g_ssv (syn_crn (syn_cwpppowsetfn))
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv)) p0001 p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv))))
  have p0005 :=
    @g_mpbir (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv)) (syn_wa (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv))) p0003 p0004
  have p0006 :=
    @g_sifmap (syn_cvv) (syn_cvv) (syn_cwpppowsetfn)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_ffn (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwpppowsetfn))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_ssv (syn_crn (syn_csi (syn_cwpppowsetfn)))
  have p0011 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_csi (syn_cwpppowsetfn)) (syn_cpw1 (syn_cvv))) (syn_wss (syn_crn (syn_csi (syn_cwpppowsetfn))) (syn_cvv)) p0000 p0009 p0010
  have p0012 :=
    @g_fnco (syn_cvv) (syn_cpw1 (syn_cvv)) (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    (by simpa [syn_cwpppowset2fn] using (Nominal.classEqRefl (syn_cwpppowset2fn)))
  have p0015 :=
    @g_fneq1i (syn_cpw1 (syn_cvv)) (syn_cwpppowset2fn) (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) p0014
  have p0016 :=
    @g_mpbir (syn_wfn (syn_cwpppowset2fn) (syn_cpw1 (syn_cvv))) (syn_wfn (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_cpw1 (syn_cvv))) p0013 p0015
  exact p0016

noncomputable def g_wpppowset2fnvalndv
    (A : Class) (hyp_wpppowset2fnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn A))) (syn_cpw (syn_cpw A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cwpppowset2fn] using (Nominal.classEqRefl (syn_cwpppowset2fn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn A)) (syn_cwpppowset2fn) (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) p0000
  have p0002 :=
    @g_wpppowsetfnfnndv
  have p0003 :=
    @g_ssv (syn_crn (syn_cwpppowsetfn))
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv)) p0002 p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv))))
  have p0006 :=
    @g_mpbir (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv)) (syn_wa (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv))) p0004 p0005
  have p0007 :=
    @g_sifmap (syn_cvv) (syn_cvv) (syn_cwpppowsetfn)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_ffn (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwpppowsetfn))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_snex A
  have p0012 :=
    @g_snelpw1 (syn_csn A) (syn_cvv)
  have p0013 :=
    @g_mpbir (.classMem (syn_csn (syn_csn A)) (syn_cpw1 (syn_cvv))) (.classMem (syn_csn A) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_csi (syn_cwpppowsetfn)) (syn_cpw1 (syn_cvv))) (.classMem (syn_csn (syn_csn A)) (syn_cpw1 (syn_cvv))) p0010 p0013
  have p0015 :=
    @g_fvco2 (syn_cpw1 (syn_cvv)) (syn_csn (syn_csn A)) (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_snex A
  have p0018 :=
    @g_wpppowsetfnfnndv
  have p0019 :=
    @g_ssv (syn_crn (syn_cwpppowsetfn))
  have p0020 :=
    @g_pm3_2i (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv)) p0018 p0019
  have p0021 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv))))
  have p0022 :=
    @g_mpbir (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv)) (syn_wa (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv))) p0020 p0021
  have p0023 :=
    @g_sifvald (syn_cvv) (syn_cvv) (syn_csn A) (syn_cwpppowsetfn) p0022
  have p0024 :=
    Nominal.mp p0017 p0023
  have p0025 :=
    @g_wpppowsetfnvalndv A hyp_wpppowset2fnvalndv_1
  have p0026 :=
    @g_sneqi (syn_cfv (syn_cwpppowsetfn) (syn_csn A)) (syn_cpw A) p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_csi (syn_cwpppowsetfn)) (syn_csn (syn_csn A))) (syn_csn (syn_cfv (syn_cwpppowsetfn) (syn_csn A))) (syn_csn (syn_cpw A)) p0024 p0026
  have p0028 :=
    @g_fveq2i (syn_cfv (syn_csi (syn_cwpppowsetfn)) (syn_csn (syn_csn A))) (syn_csn (syn_cpw A)) (syn_cwpppowsetfn) p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_csn (syn_csn A))) (syn_cfv (syn_cwpppowsetfn) (syn_cfv (syn_csi (syn_cwpppowsetfn)) (syn_csn (syn_csn A)))) (syn_cfv (syn_cwpppowsetfn) (syn_csn (syn_cpw A))) p0016 p0028
  have p0030 :=
    @g_pwex A hyp_wpppowset2fnvalndv_1
  have p0031 :=
    @g_wpppowsetfnvalndv (syn_cpw A) p0030
  have p0032 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_csn (syn_csn A))) (syn_cfv (syn_cwpppowsetfn) (syn_csn (syn_cpw A))) (syn_cpw (syn_cpw A)) p0029 p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn A))) (syn_cfv (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_csn (syn_csn A))) (syn_cpw (syn_cpw A)) p0001 p0032
  exact p0033

noncomputable def g_wpppowset2fnvalimpndv
    (q : Var) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv q)) (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv q))))))) := by
  let proofSupport : Finset Var := ({q} : Finset Var)
  have dv_cache_0001 : q ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdcolcodearg (syn_cvv) q dv_cache_0001
  have p0001 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv)) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0002 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv)) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0000 p0001
  have p0003 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cwpppowset2fn) p0002
  have p0004 :=
    @g_vex q
  have p0005 :=
    @g_uniex (.cv q) p0004
  have p0006 :=
    @g_uniex (syn_cuni (.cv q)) p0005
  have p0007 :=
    @g_wpppowset2fnvalndv (syn_cuni (syn_cuni (.cv q))) p0006
  have p0008 :=
    @g_a1i (.classEq (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv q)))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0007
  have p0009 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cfv (syn_cwpppowset2fn) (.cv q)) (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv q))))) p0003 p0008
  exact p0009

noncomputable def g_wpppowset2imexndv
    (Q : Class) (hyp_wpppowset2imexndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) (syn_cvv)) := by
  let proofSupport : Finset Var := Q.fv
  have p0000 :=
    @g_wpppowset2fnexndv
  have p0001 :=
    @g_pw1ex Q hyp_wpppowset2imexndv_1
  have p0002 :=
    @g_pw1ex (syn_cpw1 Q) p0001
  have p0003 :=
    @g_imaex (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)) p0000 p0002
  exact p0003

noncomputable def g_wpppowset2imcanndv
    (C : Class) (Q : Class) (hyp_wpppowset2imcanndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) (hyp_wpppowset2imcanndv_2 : Nominal.NPrf (.classMem C Q)) :
    Nominal.NPrf (.classMem (syn_cpw (syn_cpw C)) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))) := by
  let proofSupport : Finset Var := C.fv ∪ Q.fv
  have p0000 :=
    @g_elexi C Q hyp_wpppowset2imcanndv_2
  have p0001 :=
    @g_wpppowset2fnvalndv C p0000
  have p0002 :=
    @g_eqcomi (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn C))) (syn_cpw (syn_cpw C)) p0001
  have p0003 :=
    @g_snelpw1 C Q
  have p0004 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 Q)) (.classMem C Q) hyp_wpppowset2imcanndv_2 p0003
  have p0005 :=
    @g_snelpw1 (syn_csn C) (syn_cpw1 Q)
  have p0006 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cpw1 Q))) (.classMem (syn_csn C) (syn_cpw1 Q)) p0004 p0005
  have p0007 :=
    @g_wpppowset2fnfnndv
  have p0008 :=
    @g_fnfun (syn_cpw1 (syn_cvv)) (syn_cwpppowset2fn)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_snex C
  have p0011 :=
    @g_snelpw1 (syn_csn C) (syn_cvv)
  have p0012 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cvv))) (.classMem (syn_csn C) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_wpppowset2fnfnndv
  have p0014 :=
    @g_fndm (syn_cpw1 (syn_cvv)) (syn_cwpppowset2fn)
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_eleq2i (syn_cdm (syn_cwpppowset2fn)) (syn_cpw1 (syn_cvv)) (syn_csn (syn_csn C)) p0015
  have p0017 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cdm (syn_cwpppowset2fn))) (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cvv))) p0012 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfun (syn_cwpppowset2fn)) (.classMem (syn_csn (syn_csn C)) (syn_cdm (syn_cwpppowset2fn))) p0009 p0017
  have p0019 :=
    @g_funfvima (syn_cpw1 (syn_cpw1 Q)) (syn_csn (syn_csn C)) (syn_cwpppowset2fn)
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    Nominal.mp p0006 p0020
  have p0022 :=
    @g_eqeltri (syn_cpw (syn_cpw C)) (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn C))) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) p0002 p0021
  exact p0022

#print axioms g_wpppowset2imcanndv

end NFChoice.DirectNominalPrf.WPPReplay
