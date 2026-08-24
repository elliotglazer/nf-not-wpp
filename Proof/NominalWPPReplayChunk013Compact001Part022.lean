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
import NominalWPPReplayChunk013Compact001Part021

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

noncomputable def g_foundex
     :
    Nominal.NPrf (.classMem (syn_cfound) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let r : Var := freshVar proofSupport 4
  let t : Var := freshVar proofSupport 5
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
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
  have fresh_x_ne_r : x ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_a_ne_y : a ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_z : a ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_ne_r : a ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_r_ne_a : r ≠ a :=
    Ne.symm fresh_a_ne_r
  have fresh_a_ne_t : a ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_t_ne_a : t ≠ a :=
    Ne.symm fresh_a_ne_t
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_r : y ≠ r := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_z_ne_r : z ≠ r := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_r_ne_z : r ≠ z :=
    Ne.symm fresh_z_ne_r
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_r_ne_t : r ≠ t := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_t_ne_r : t ≠ r :=
    Ne.symm fresh_r_ne_t
  have dv_cache_0001 : a ≠ r := by
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0004 : a ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0005 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0006 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0007 : r ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0010 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : x ∉ ((syn_cop (.cv r) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : t ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : t ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_cop (.cv x) (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : r ∉ ((syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : a ∉ ((syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_found x y z r a dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_vex r
  have p0002 :=
    @g_vex a
  have p0003 :=
    @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a)) (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))) p0003
  have p0005 :=
    @g_elrn2 x (syn_cop (.cv r) (.cv a)) (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))) dv_cache_0011 dv_cache_0012
  have p0006 :=
    @g_oteltxp (.cv x) (.cv r) (.cv a) (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_opex (.cv x) (.cv r) p0007 p0001
  have p0009 :=
    @g_elcompl (syn_cop (.cv x) (.cv r)) (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)) p0008
  have p0010 :=
    @g_elin (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))
  have p0011 :=
    @g_otelins3 (syn_csn (.cv z)) (.cv x) (.cv r) (syn_csset) p0001
  have p0012 :=
    @g_vex z
  have p0013 :=
    @g_opelssetsn (.cv z) (.cv x) p0012 p0007
  have p0014_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)) :=
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
      p0013
  have p0014 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cins3 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x) p0011 p0014_e01_recanon
  have p0015 :=
    @g_snex (.cv z)
  have p0016 :=
    @g_opex (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)) p0015 p0008
  have p0017 :=
    @g_elcompl (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)) p0016
  have p0018 :=
    @g_elin (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))
  have p0019 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)) (syn_cins3 (syn_csset)) p0015
  have p0020 :=
    @g_otelins3 (syn_csn (.cv y)) (.cv x) (.cv r) (syn_csset) p0001
  have p0021 :=
    @g_vex y
  have p0022 :=
    @g_opelssetsn (.cv y) (.cv x) p0021 p0007
  have p0023_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x)) :=
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
      p0022
  have p0023 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins2 (syn_cins3 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) (.cv r))) (syn_cins3 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x) p0019 p0020 p0023_e02_recanon
  have p0024 :=
    @g_eldif (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid))
  have p0025 :=
    @g_elin (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))
  have p0026 :=
    @g_oqelins4 (syn_csn (.cv t)) (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)) (syn_csi3 (syn_cid)) p0008
  have p0027 :=
    @g_vex t
  have p0028 :=
    @g_otsnelsi3 (.cv t) (.cv y) (.cv z) (syn_cid) p0027 p0021 p0012
  have p0029 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv t) (syn_cid) (syn_cop (.cv y) (.cv z)))))
  have p0030 :=
    @g_opex (.cv y) (.cv z) p0021 p0012
  have p0031 :=
    @g_ideq (.cv t) (syn_cop (.cv y) (.cv z)) p0030
  have p0032 :=
    @g_bitr3i (.classMem (syn_cop (.cv t) (syn_cop (.cv y) (.cv z))) (syn_cid)) (syn_wbr (.cv t) (syn_cid) (syn_cop (.cv y) (.cv z))) (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) p0029 p0031
  have p0033 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z)))) (syn_csi3 (syn_cid))) (.classMem (syn_cop (.cv t) (syn_cop (.cv y) (.cv z))) (syn_cid)) (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) p0026 p0028 p0032
  have p0034 :=
    @g_snex (.cv y)
  have p0035 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cins2 (syn_cins2 (syn_csset))) p0034
  have p0036 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)) (syn_cins2 (syn_csset)) p0015
  have p0037 :=
    @g_otelins2 (syn_csn (.cv t)) (.cv x) (.cv r) (syn_csset) p0007
  have p0038 :=
    @g_opelssetsn (.cv t) (.cv r) p0027 p0001
  have p0039_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset)) (.objMem t r)) :=
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
      p0038
  have p0039 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (.cv x) (.cv r))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset)) (.objMem t r) p0037 p0039_e01_recanon
  have p0040 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (.cv x) (.cv r))) (syn_cins2 (syn_csset))) (.objMem t r) p0035 p0036 p0039
  have p0041 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (.objMem t r) p0033 p0040
  have p0042 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r)) p0025 p0041
  have p0043 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r)) t p0042
  have p0044 :=
    @g_elima1c t (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) dv_cache_0013 dv_cache_0014
  have p0045 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv z))))
  have p0046 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV t (syn_cop (.cv y) (.cv z)) (.cv r) dv_cache_0015 dv_cache_0016))
  have p0047_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv y) (.cv z)) (.cv r)) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r)))) :=
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
      p0046
  have p0047 :=
    @g_bitri (syn_wbr (.cv y) (.cv r) (.cv z)) (.classMem (syn_cop (.cv y) (.cv z)) (.cv r)) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r))) p0045 p0047_e01_recanon
  have p0048 :=
    @g_n_3bitr4i (syn_wex t (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))) (syn_wbr (.cv y) (.cv r) (.cv z)) p0043 p0044 p0047
  have p0049 :=
    @g_otelins3 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)) (syn_cid) p0008
  have p0050 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z)))))
  have p0051 :=
    @g_ideq (syn_csn (.cv y)) (syn_csn (.cv z)) p0015
  have p0052 :=
    @g_sneqb (.cv y) (.cv z) p0021
  have p0053_e01_recanon : Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0052
  have p0053 :=
    @g_bitri (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z))) (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z) p0051 p0053_e01_recanon
  have p0054 :=
    @g_bitr3i (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z))) (syn_cid)) (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z))) (.objEq y z) p0050 p0053
  have p0055 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins3 (syn_cid))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z))) (syn_cid)) (.objEq y z) p0049 p0054
  have p0056 :=
    @g_notbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins3 (syn_cid))) (.objEq y z) p0055
  have p0057 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))) (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins3 (syn_cid)))) (.neg (.objEq y z)) p0048 p0056
  have p0058 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))) (.neg (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins3 (syn_cid))))) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))) p0024 p0057
  have p0059 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins2 (syn_cins3 (syn_csset)))) (.objMem y x) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))) p0023 p0058
  have p0060 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins2 (syn_cins3 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid))))) (syn_wa (.objMem y x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))) p0018 p0059
  have p0061 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid))))) (syn_wa (.objMem y x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))) y p0060
  have p0062 :=
    @g_elima1c y (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) dv_cache_0017 dv_cache_0018
  have p0063 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (.cv x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))))
  have p0064_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex y (.cv x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))) (syn_wex y (syn_wa (.objMem y x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0063
  have p0064 :=
    @g_n_3bitr4i (syn_wex y (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))))) (syn_wex y (syn_wa (.objMem y x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c))) (syn_wrex y (.cv x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))) p0061 p0062 p0064_e02_recanon
  have p0065 :=
    @g_rexanali (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z) y (.cv x)
  have p0066 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c))) (syn_wrex y (.cv x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))) (.neg (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))) p0064 p0065
  have p0067 :=
    @g_con2bii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c))) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))) p0066
  have p0068 :=
    @g_bitr4i (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (.neg (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))) p0017 p0067
  have p0069 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cins3 (syn_csset))) (.objMem z x) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))) p0014 p0068
  have p0070 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cins3 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c))))) (syn_wa (.objMem z x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))) p0010 p0069
  have p0071 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c))))) (syn_wa (.objMem z x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))) z p0070
  have p0072 :=
    @g_elima1c z (syn_cop (.cv x) (.cv r)) (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) dv_cache_0019 dv_cache_0020
  have p0073 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
  have p0074_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))) (syn_wex z (syn_wa (.objMem z x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0073
  have p0074 :=
    @g_n_3bitr4i (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))))) (syn_wex z (syn_wa (.objMem z x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))) (.classMem (syn_cop (.cv x) (.cv r)) (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))) p0071 p0072 p0074_e02_recanon
  have p0075 :=
    @g_notbii (.classMem (syn_cop (.cv x) (.cv r)) (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))) p0074
  have p0076 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv r)) (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))) (.neg (.classMem (syn_cop (.cv x) (.cv r)) (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))) (.neg (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))) p0009 p0075
  have p0077 :=
    @g_elin (syn_cop (.cv x) (.cv a)) (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))
  have p0078 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csset) (.cv a))))
  have p0079 :=
    @g_brsset (.cv x) (.cv a) p0007 p0002
  have p0080 :=
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv a)) (syn_csset)) (syn_wbr (.cv x) (syn_csset) (.cv a)) (syn_wss (.cv x) (.cv a)) p0078 p0079
  have p0081 :=
    @g_opelxp (.cv x) (.cv a) (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)
  have p0082 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv x) (.cv a)) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))) (.classMem (.cv x) (syn_ccompl (syn_csn (syn_c0)))) (.classMem (.cv a) (syn_cvv)) p0002 p0081
  have p0083 :=
    @g_elcompl (.cv x) (syn_csn (syn_c0)) p0007
  have p0084 :=
    @g_elsn x (syn_c0) dv_cache_0021
  have p0085 :=
    @g_necon3bbii (.classMem (.cv x) (syn_csn (syn_c0))) (.cv x) (syn_c0) p0084
  have p0086 :=
    @g_n_3bitri (.classMem (syn_cop (.cv x) (.cv a)) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))) (.classMem (.cv x) (syn_ccompl (syn_csn (syn_c0)))) (.neg (.classMem (.cv x) (syn_csn (syn_c0)))) (syn_wne (.cv x) (syn_c0)) p0082 p0083 p0085
  have p0087 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv a)) (syn_csset)) (syn_wss (.cv x) (.cv a)) (.classMem (syn_cop (.cv x) (.cv a)) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))) (syn_wne (.cv x) (syn_c0)) p0080 p0086
  have p0088 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv a)) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))) (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) (syn_csset)) (.classMem (syn_cop (.cv x) (.cv a)) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))) (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) p0077 p0087
  have p0089 :=
    @g_anbi12ci (.classMem (syn_cop (.cv x) (.cv r)) (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))) (.neg (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))) (.classMem (syn_cop (.cv x) (.cv a)) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))) (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) p0076 p0088
  have p0090 :=
    @g_bitri (.classMem (syn_cop (.cv x) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))) (syn_wa (.classMem (syn_cop (.cv x) (.cv r)) (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))) (.classMem (syn_cop (.cv x) (.cv a)) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))) (syn_wa (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (.neg (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))) p0006 p0089
  have p0091 :=
    @g_exbii (.classMem (syn_cop (.cv x) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))) (syn_wa (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (.neg (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))) x p0090
  have p0092 :=
    @g_exanali (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))) x
  have p0093 :=
    @g_n_3bitri (.classMem (syn_cop (.cv r) (.cv a)) (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wex x (.classMem (syn_cop (.cv x) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wex x (syn_wa (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (.neg (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))) (.neg (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))) p0005 p0091 p0092
  have p0094 :=
    @g_con2bii (.classMem (syn_cop (.cv r) (.cv a)) (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))) (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))) p0093
  have p0095 :=
    @g_bitr4i (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))) (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))) (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))) p0004 p0094
  have p0096 :=
    @g_opabbi2i (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))) r a (syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))) dv_cache_0022 dv_cache_0023 dv_cache_0024 p0095
  have p0097 :=
    @g_eqtr4i (syn_cfound) (syn_copab r a (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))) (syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))) p0000 p0096
  have p0098 :=
    @g_ssetex
  have p0099 :=
    @g_ins3ex (syn_csset) p0098
  have p0100 :=
    @g_ins2ex (syn_cins3 (syn_csset)) p0099
  have p0101 :=
    @g_idex
  have p0102 :=
    @g_si3ex (syn_cid) p0101
  have p0103 :=
    @g_ins4ex (syn_csi3 (syn_cid)) p0102
  have p0104 :=
    @g_ssetex
  have p0105 :=
    @g_ins2ex (syn_csset) p0104
  have p0106 :=
    @g_ins2ex (syn_cins2 (syn_csset)) p0105
  have p0107 :=
    @g_ins2ex (syn_cins2 (syn_cins2 (syn_csset))) p0106
  have p0108 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) p0103 p0107
  have p0109 :=
    @g_n_1cex
  have p0110 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c) p0108 p0109
  have p0111 :=
    @g_idex
  have p0112 :=
    @g_ins3ex (syn_cid) p0111
  have p0113 :=
    @g_difex (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)) p0110 p0112
  have p0114 :=
    @g_inex (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid))) p0100 p0113
  have p0115 :=
    @g_n_1cex
  have p0116 :=
    @g_imaex (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c) p0114 p0115
  have p0117 :=
    @g_complex (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)) p0116
  have p0118 :=
    @g_inex (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c))) p0099 p0117
  have p0119 :=
    @g_n_1cex
  have p0120 :=
    @g_imaex (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c) p0118 p0119
  have p0121 :=
    @g_complex (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)) p0120
  have p0122 :=
    @g_ssetex
  have p0123 :=
    @g_snex (syn_c0)
  have p0124 :=
    @g_complex (syn_csn (syn_c0)) p0123
  have p0125 :=
    @g_vvex
  have p0126 :=
    @g_xpex (syn_ccompl (syn_csn (syn_c0))) (syn_cvv) p0124 p0125
  have p0127 :=
    @g_inex (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)) p0122 p0126
  have p0128 :=
    @g_txpex (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))) p0121 p0127
  have p0129 :=
    @g_rnex (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))) p0128
  have p0130 :=
    @g_complex (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))) p0129
  have p0131 :=
    @g_eqeltri (syn_cfound) (syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cvv) p0097 p0130
  exact p0131

#print axioms g_foundex

end NFChoice.DirectNominalPrf.WPPReplay
