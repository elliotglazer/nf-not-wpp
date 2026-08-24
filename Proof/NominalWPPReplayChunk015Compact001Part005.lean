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
import NominalWPPReplayChunk015Compact001Part004

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

noncomputable def g_lnkerexg
    (R : Class) :
    Nominal.NPrf (.imp (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv))) := by
  let proofSupport : Finset Var := R.fv
  have p0000 :=
    (by simpa [syn_clnker] using (Nominal.classEqRefl (syn_clnker R)))
  have p0001 :=
    @g_id (.classMem R (syn_cvv))
  have p0002 :=
    @g_cnvexg R (syn_cvv)
  have p0003 :=
    @g_jca (.classMem R (syn_cvv)) (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_inexg R (syn_ccnv R) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem R (syn_cvv)) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv))) (.classMem (syn_cin R (syn_ccnv R)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (.classMem R (syn_cvv)) (syn_clnker R) (syn_cin R (syn_ccnv R)) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_brlnqrelkern
    (C : Class) (R : Class) (X : Class) (Y : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R))) (syn_wbr X R Y))) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_X : u ∉ X.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_Y : u ∉ Y.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_X : v ∉ X.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_Y : v ∉ Y.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have dv_cache_0001 : u ∉ ((syn_cec X (syn_clnker R))).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_X, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((syn_cec X (syn_clnker R))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_X, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_cec Y (syn_clnker R))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_Y, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((syn_cec Y (syn_clnker R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_Y, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0008 : u ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ (Y).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_Y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : v ∉ (Y).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_Y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0001 :=
    (by simpa [syn_clnker] using (Nominal.classEqRefl (syn_clnker R)))
  have p0002 :=
    @g_id (.classMem R (syn_cvv))
  have p0003 :=
    @g_cnvexg R (syn_cvv)
  have p0004 :=
    @g_jca (.classMem R (syn_cvv)) (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_inexg R (syn_ccnv R) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem R (syn_cvv)) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv))) (.classMem (syn_cin R (syn_ccnv R)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_syl5eqel (.classMem R (syn_cvv)) (syn_clnker R) (syn_cin R (syn_ccnv R)) (syn_cvv) p0001 p0006
  have p0008 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0000 p0007
  have p0009 :=
    @g_ecexg X (syn_cvv) (syn_clnker R)
  have p0010 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem (syn_clnker R) (syn_cvv)) (.classMem (syn_cec X (syn_clnker R)) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_simpl (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0012 :=
    (by simpa [syn_clnker] using (Nominal.classEqRefl (syn_clnker R)))
  have p0013 :=
    @g_id (.classMem R (syn_cvv))
  have p0014 :=
    @g_cnvexg R (syn_cvv)
  have p0015 :=
    @g_jca (.classMem R (syn_cvv)) (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_inexg R (syn_ccnv R) (syn_cvv) (syn_cvv)
  have p0017 :=
    @g_syl (.classMem R (syn_cvv)) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv))) (.classMem (syn_cin R (syn_ccnv R)) (syn_cvv)) p0015 p0016
  have p0018 :=
    @g_syl5eqel (.classMem R (syn_cvv)) (syn_clnker R) (syn_cin R (syn_ccnv R)) (syn_cvv) p0012 p0017
  have p0019 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0011 p0018
  have p0020 :=
    @g_ecexg Y (syn_cvv) (syn_clnker R)
  have p0021 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem (syn_clnker R) (syn_cvv)) (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_jca (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem (syn_cec X (syn_clnker R)) (syn_cvv)) (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv)) p0010 p0021
  have p0023 :=
    @g_brlnqrelg u v (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) R (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0024 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wa (.classMem (syn_cec X (syn_clnker R)) (syn_cvv)) (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv))) (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R))) (syn_wrex u (syn_cec X (syn_clnker R)) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v))))) p0022 p0023
  have p0025 :=
    @g_simpr (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0026 :=
    @g_lnqrelreps v u C R X Y dv_cache_0008 dv_cache_0009 dv_cache_0005 dv_cache_0006 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0007
  have p0027 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wb (syn_wrex u (syn_cec X (syn_clnker R)) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v)))) (syn_wbr X R Y)) p0025 p0026
  have p0028 :=
    @g_bitrd (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R))) (syn_wrex u (syn_cec X (syn_clnker R)) (syn_wrex v (syn_cec Y (syn_clnker R)) (syn_wbr (.cv u) R (.cv v)))) (syn_wbr X R Y) p0024 p0027
  exact p0028

#print axioms g_brlnqrelkern

end NFChoice.DirectNominalPrf.WPPReplay
