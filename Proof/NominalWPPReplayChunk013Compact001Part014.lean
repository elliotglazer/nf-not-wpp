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
import NominalWPPReplayChunk013Compact001Part013

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

noncomputable def g_domfnex
     :
    Nominal.NPrf (.classMem (syn_cdomfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : w ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_cdm (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0001 :=
    @g_elin (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_oqelins4 (syn_csn (.cv w)) (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv x) (syn_csi3 (syn_cswap)) p0002
  have p0004 :=
    @g_vex w
  have p0005 :=
    @g_vex z
  have p0006 :=
    @g_vex y
  have p0007 :=
    @g_otsnelsi3 (.cv w) (.cv z) (.cv y) (syn_cswap) p0004 p0005 p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv w) (syn_cswap) (syn_cop (.cv z) (.cv y)))))
  have p0009 :=
    @g_brswap2 (.cv w) (.cv z) (.cv y) p0005 p0006
  have p0010 :=
    @g_n_3bitr2i (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y)))) (syn_csi3 (syn_cswap))) (.classMem (syn_cop (.cv w) (syn_cop (.cv z) (.cv y))) (syn_cswap)) (syn_wbr (.cv w) (syn_cswap) (syn_cop (.cv z) (.cv y))) (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) p0007 p0008 p0009
  have p0011 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cswap)))) (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y)))) (syn_csi3 (syn_cswap))) (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) p0003 p0010
  have p0012 :=
    @g_snex (.cv z)
  have p0013 :=
    @g_otelins2 (syn_csn (.cv w)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cins2 (syn_csset)) p0012
  have p0014 :=
    @g_snex (.cv y)
  have p0015 :=
    @g_otelins2 (syn_csn (.cv w)) (syn_csn (.cv y)) (.cv x) (syn_csset) p0014
  have p0016 :=
    @g_opelssetsn (.cv w) (.cv x) p0004 p0002
  have p0017_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv w)) (.cv x)) (syn_csset)) (.objMem w x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0017 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv w)) (.cv x)) (syn_csset)) (.objMem w x) p0015 p0017_e01_recanon
  have p0018 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins2 (syn_csset))) (.objMem w x) p0013 p0017
  have p0019 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cswap)))) (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem w x) p0011 p0018
  have p0020 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cswap)))) (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (.objMem w x)) p0001 p0019
  have p0021 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (.objMem w x)) w p0020
  have p0022 :=
    @g_elima1c w (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) dv_cache_0001 dv_cache_0002
  have p0023 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w (syn_cop (.cv y) (.cv z)) (.cv x) dv_cache_0003 dv_cache_0004))
  have p0024_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (.objMem w x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0023
  have p0024 :=
    @g_n_3bitr4i (syn_wex w (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (.objMem w x))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) p0021 p0022 p0024_e02_recanon
  have p0025 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) z p0024
  have p0026 :=
    @g_elima1c z (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) dv_cache_0005 dv_cache_0006
  have p0027 :=
    @g_eldm2 z (.cv y) (.cv x) dv_cache_0007 dv_cache_0008
  have p0028 :=
    @g_n_3bitr4i (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))) (.classMem (.cv y) (syn_cdm (.cv x))) p0025 p0026 p0027
  have p0029 :=
    @g_releqmpt x y (syn_cvv) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c)) (syn_cdm (.cv x)) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 p0028
  have p0030 :=
    @g_eqtr4i (syn_cdomfn) (syn_cmpt x (syn_cvv) (syn_cdm (.cv x))) (syn_cin (syn_cxp (syn_cvv) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c)))) (syn_c1c))))) p0000 p0029
  have p0031 :=
    @g_vvex
  have p0032 :=
    @g_swapex
  have p0033 :=
    @g_si3ex (syn_cswap) p0032
  have p0034 :=
    @g_ins4ex (syn_csi3 (syn_cswap)) p0033
  have p0035 :=
    @g_ssetex
  have p0036 :=
    @g_ins2ex (syn_csset) p0035
  have p0037 :=
    @g_ins2ex (syn_cins2 (syn_csset)) p0036
  have p0038 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))) p0034 p0037
  have p0039 :=
    @g_n_1cex
  have p0040 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c) p0038 p0039
  have p0041 :=
    @g_n_1cex
  have p0042 :=
    @g_imaex (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c) p0040 p0041
  have p0043 :=
    @g_mptexlem (syn_cvv) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c)) p0031 p0042
  have p0044 :=
    @g_eqeltri (syn_cdomfn) (syn_cin (syn_cxp (syn_cvv) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c)))) (syn_c1c))))) (syn_cvv) p0030 p0043
  exact p0044

noncomputable def g_ranfnex
     :
    Nominal.NPrf (.classMem (syn_cranfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : w ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((syn_cop (.cv z) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_crn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0001 :=
    @g_elin (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_oqelins4 (syn_csn (.cv w)) (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv x) (syn_csi3 (syn_cid)) p0002
  have p0004 :=
    @g_vex w
  have p0005 :=
    @g_vex z
  have p0006 :=
    @g_vex y
  have p0007 :=
    @g_otsnelsi3 (.cv w) (.cv z) (.cv y) (syn_cid) p0004 p0005 p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv w) (syn_cid) (syn_cop (.cv z) (.cv y)))))
  have p0009 :=
    @g_opex (.cv z) (.cv y) p0005 p0006
  have p0010 :=
    @g_ideq (.cv w) (syn_cop (.cv z) (.cv y)) p0009
  have p0011 :=
    @g_n_3bitr2i (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y)))) (syn_csi3 (syn_cid))) (.classMem (syn_cop (.cv w) (syn_cop (.cv z) (.cv y))) (syn_cid)) (syn_wbr (.cv w) (syn_cid) (syn_cop (.cv z) (.cv y))) (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) p0007 p0008 p0010
  have p0012 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y)))) (syn_csi3 (syn_cid))) (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) p0003 p0011
  have p0013 :=
    @g_snex (.cv z)
  have p0014 :=
    @g_otelins2 (syn_csn (.cv w)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cins2 (syn_csset)) p0013
  have p0015 :=
    @g_snex (.cv y)
  have p0016 :=
    @g_otelins2 (syn_csn (.cv w)) (syn_csn (.cv y)) (.cv x) (syn_csset) p0015
  have p0017 :=
    @g_opelssetsn (.cv w) (.cv x) p0004 p0002
  have p0018_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv w)) (.cv x)) (syn_csset)) (.objMem w x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0017
  have p0018 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv w)) (.cv x)) (syn_csset)) (.objMem w x) p0016 p0018_e01_recanon
  have p0019 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins2 (syn_csset))) (.objMem w x) p0014 p0018
  have p0020 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem w x) p0012 p0019
  have p0021 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (.objMem w x)) p0001 p0020
  have p0022 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (.objMem w x)) w p0021
  have p0023 :=
    @g_elima1c w (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) dv_cache_0001 dv_cache_0002
  have p0024 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w (syn_cop (.cv z) (.cv y)) (.cv x) dv_cache_0003 dv_cache_0004))
  have p0025_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv z) (.cv y)) (.cv x)) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (.objMem w x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0024
  have p0025 :=
    @g_n_3bitr4i (syn_wex w (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (.objMem w x))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (.classMem (syn_cop (.cv z) (.cv y)) (.cv x)) p0022 p0023 p0025_e02_recanon
  have p0026 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (.classMem (syn_cop (.cv z) (.cv y)) (.cv x)) z p0025
  have p0027 :=
    @g_elima1c z (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) dv_cache_0005 dv_cache_0006
  have p0028 :=
    @g_elrn2 z (.cv y) (.cv x) dv_cache_0007 dv_cache_0008
  have p0029 :=
    @g_n_3bitr4i (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_wex z (.classMem (syn_cop (.cv z) (.cv y)) (.cv x))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))) (.classMem (.cv y) (syn_crn (.cv x))) p0026 p0027 p0028
  have p0030 :=
    @g_releqmpt x y (syn_cvv) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c)) (syn_crn (.cv x)) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 p0029
  have p0031 :=
    @g_eqtr4i (syn_cranfn) (syn_cmpt x (syn_cvv) (syn_crn (.cv x))) (syn_cin (syn_cxp (syn_cvv) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c)))) (syn_c1c))))) p0000 p0030
  have p0032 :=
    @g_vvex
  have p0033 :=
    @g_idex
  have p0034 :=
    @g_si3ex (syn_cid) p0033
  have p0035 :=
    @g_ins4ex (syn_csi3 (syn_cid)) p0034
  have p0036 :=
    @g_ssetex
  have p0037 :=
    @g_ins2ex (syn_csset) p0036
  have p0038 :=
    @g_ins2ex (syn_cins2 (syn_csset)) p0037
  have p0039 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))) p0035 p0038
  have p0040 :=
    @g_n_1cex
  have p0041 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c) p0039 p0040
  have p0042 :=
    @g_n_1cex
  have p0043 :=
    @g_imaex (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c) p0041 p0042
  have p0044 :=
    @g_mptexlem (syn_cvv) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c)) p0032 p0043
  have p0045 :=
    @g_eqeltri (syn_cranfn) (syn_cin (syn_cxp (syn_cvv) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c)))) (syn_c1c))))) (syn_cvv) p0031 p0044
  exact p0045

noncomputable def g_clos1eq1
    (R : Class) (S : Class) (T : Class) :
    Nominal.NPrf (.imp (.classEq S T) (.classEq (syn_cclos1 S R) (syn_cclos1 T R))) := by
  let proofSupport : Finset Var := R.fv ∪ S.fv ∪ T.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_T : a ∉ T.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : a ∉ ((Wff.classEq S T)).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, fresh_a_not_T, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ (T).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_T, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_sseq1 S T (.cv a)
  have p0001 :=
    @g_anbi1d (.classEq S T) (syn_wss S (.cv a)) (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)) p0000
  have p0002 :=
    @g_abbidv (.classEq S T) (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) a dv_cache_0001 p0001
  have p0003 :=
    @g_inteq (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))) (.cab a (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
  have p0004 :=
    @g_syl (.classEq S T) (.classEq (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))) (.cab a (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (.classEq (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_cint (.cab a (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))) p0002 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R T a dv_cache_0002 dv_cache_0004
  have p0007 :=
    @g_n_3eqtr4g (.classEq S T) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_cint (.cab a (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_cclos1 S R) (syn_cclos1 T R) p0004 p0005 p0006
  exact p0007

noncomputable def g_clos1eq2
    (R : Class) (S : Class) (T : Class) :
    Nominal.NPrf (.imp (.classEq R T) (.classEq (syn_cclos1 S R) (syn_cclos1 S T))) := by
  let proofSupport : Finset Var := R.fv ∪ S.fv ∪ T.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_T : a ∉ T.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : a ∉ ((Wff.classEq R T)).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, fresh_a_not_T, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ (T).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_T, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_imaeq1 R T (.cv a)
  have p0001 :=
    @g_sseq1d (.classEq R T) (syn_cima R (.cv a)) (syn_cima T (.cv a)) (.cv a) p0000
  have p0002 :=
    @g_anbi2d (.classEq R T) (syn_wss (syn_cima R (.cv a)) (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a)) (syn_wss S (.cv a)) p0001
  have p0003 :=
    @g_abbidv (.classEq R T) (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a))) a dv_cache_0001 p0002
  have p0004 :=
    @g_inteq (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))) (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a))))
  have p0005 :=
    @g_syl (.classEq R T) (.classEq (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))) (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a))))) (.classEq (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a)))))) p0003 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a dv_cache_0002 dv_cache_0003
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 T S a dv_cache_0004 dv_cache_0003
  have p0008 :=
    @g_n_3eqtr4g (.classEq R T) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a))))) (syn_cclos1 S R) (syn_cclos1 S T) p0005 p0006 p0007
  exact p0008

#print axioms g_clos1eq2

end NFChoice.DirectNominalPrf.WPPReplay
