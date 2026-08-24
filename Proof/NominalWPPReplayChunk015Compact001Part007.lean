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
import NominalWPPReplayChunk015Compact001Part006

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

noncomputable def g_brlnqordkern
    (C : Class) (R : Class) (X : Class) (Y : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wbr X R Y))) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  have p0000 :=
    (by simpa [syn_clnqord] using (Nominal.classEqRefl (syn_clnqord R C)))
  have p0001 :=
    @g_breqi (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_clnqord R C) (syn_cin (syn_clnqrel R) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))) p0000
  have p0002 :=
    @g_brin (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_clnqrel R) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))
  have p0003 :=
    @g_bitri (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cin (syn_clnqrel R) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C)) (syn_cec Y (syn_clnker R)))) p0001 p0002
  have p0004 :=
    @g_a1i (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C)) (syn_cec Y (syn_clnker R))))) (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) p0003
  have p0005 :=
    @g_simpl (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0006 :=
    @g_lnkerexg R
  have p0007 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_simpr (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0009 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0010 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem X C) (.classMem Y C)) p0008 p0009
  have p0011 :=
    @g_simpl (.classMem X C) (.classMem Y C)
  have p0012 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wa (.classMem X C) (.classMem Y C)) (.classMem X C) p0010 p0011
  have p0013 :=
    @g_jca (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem (syn_clnker R) (syn_cvv)) (.classMem X C) p0007 p0012
  have p0014 :=
    @g_ecelqsg C X (syn_clnker R) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem X C)) (.classMem (syn_cec X (syn_clnker R)) (syn_cqs C (syn_clnker R))) p0013 p0014
  have p0016 :=
    (by simpa [syn_clnquo] using (Nominal.classEqRefl (syn_clnquo R C)))
  have p0017 :=
    @g_syl6eleqr (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_cec X (syn_clnker R)) (syn_cqs C (syn_clnker R)) (syn_clnquo R C) p0015 p0016
  have p0018 :=
    @g_simpl (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0019 :=
    @g_lnkerexg R
  have p0020 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_simpr (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0022 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0023 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem X C) (.classMem Y C)) p0021 p0022
  have p0024 :=
    @g_simpr (.classMem X C) (.classMem Y C)
  have p0025 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wa (.classMem X C) (.classMem Y C)) (.classMem Y C) p0023 p0024
  have p0026 :=
    @g_jca (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem (syn_clnker R) (syn_cvv)) (.classMem Y C) p0020 p0025
  have p0027 :=
    @g_ecelqsg C Y (syn_clnker R) (syn_cvv)
  have p0028 :=
    @g_syl (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem Y C)) (.classMem (syn_cec Y (syn_clnker R)) (syn_cqs C (syn_clnker R))) p0026 p0027
  have p0029 :=
    (by simpa [syn_clnquo] using (Nominal.classEqRefl (syn_clnquo R C)))
  have p0030 :=
    @g_syl6eleqr (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_cec Y (syn_clnker R)) (syn_cqs C (syn_clnker R)) (syn_clnquo R C) p0028 p0029
  have p0031 :=
    @g_jca (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (.classMem (syn_cec X (syn_clnker R)) (syn_clnquo R C)) (.classMem (syn_cec Y (syn_clnker R)) (syn_clnquo R C)) p0017 p0030
  have p0032 :=
    @g_brxp (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_clnquo R C) (syn_clnquo R C)
  have p0033 :=
    @g_sylibr (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wa (.classMem (syn_cec X (syn_clnker R)) (syn_clnquo R C)) (.classMem (syn_cec Y (syn_clnker R)) (syn_clnquo R C))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C)) (syn_cec Y (syn_clnker R))) p0031 p0032
  have p0034 :=
    @g_biantrud (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C)) (syn_cec Y (syn_clnker R))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R))) p0033
  have p0035 :=
    @g_bitr4d (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C)) (syn_cec Y (syn_clnker R)))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R))) p0004 p0034
  have p0036 :=
    @g_brlnqrelkern C R X Y
  have p0037 :=
    @g_bitrd (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R))) (syn_wbr X R Y) p0035 p0036
  exact p0037

noncomputable def g_lnqordref
    (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr (syn_clnqord R C) (syn_cref) (syn_clnquo R C))) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0002 : Disjoint (C).fv ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (show Disjoint (C).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((C).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (C).fv from (by exact fresh_x_not_C))))))
  have dv_cache_0003 : u ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint ((Class.cv x)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0005 : u ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((syn_wbr (.cv x) (syn_clnqord R C) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, fresh_u_not_C, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, fresh_u_not_C, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_clnquo R C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_clnqord R C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0001 :=
    @g_lnqordexg C R dv_cache_0001
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem (syn_clnqord R C) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0004 :=
    @g_lnquoexg C R dv_cache_0001
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem (syn_clnquo R C) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_ellnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0007
  have p0009 :=
    @g_biimpi (.classMem (.cv x) (syn_clnquo R C)) (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (.classMem (.cv x) (syn_clnquo R C)) (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0006 p0009
  have p0011 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0012 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0011 p0012
  have p0014 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0015 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0014 p0015
  have p0017 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0018 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0016 p0017
  have p0019 :=
    @g_simpl (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0020 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cref) C) p0018 p0019
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr R (syn_cref) C) p0013 p0020
  have p0022 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0023 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classMem (.cv u) C) p0022 p0023
  have p0025 :=
    @g_refd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) C R (.cv u) p0021 p0024
  have p0026 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0027 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0026 p0027
  have p0029 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0030 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0029 p0030
  have p0032 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0028 p0031
  have p0033 :=
    @g_breq12 (.cv x) (syn_cec (.cv u) (syn_clnker R)) (.cv x) (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (syn_wb (syn_wbr (.cv x) (syn_clnqord R C) (.cv x)) (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))) p0032 p0033
  have p0035 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0036 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0035 p0036
  have p0038 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0039 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0040 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv)) p0038 p0039
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem R (syn_cvv)) p0037 p0040
  have p0042 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0043 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0042 p0043
  have p0045 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0046 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0047 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0045 p0046
  have p0048 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0049 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0047 p0048
  have p0050 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0044 p0049
  have p0051 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0052 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0051 p0052
  have p0054 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0055 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0056 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wss R (syn_cxp C C)) p0054 p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss R (syn_cxp C C)) p0053 p0056
  have p0058 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0050 p0057
  have p0059 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0060 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classMem (.cv u) C) p0059 p0060
  have p0062 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0063 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classMem (.cv u) C) p0062 p0063
  have p0065 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classMem (.cv u) C) (.classMem (.cv u) C) p0061 p0064
  have p0066 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv u) C)) p0058 p0065
  have p0067 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv u) C))) p0041 p0066
  have p0068 :=
    @g_brlnqordkern C R (.cv u) (.cv u) dv_cache_0001
  have p0069 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv u) C)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R))) (syn_wbr (.cv u) R (.cv u))) p0067 p0068
  have p0070 :=
    @g_bitrd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wbr (.cv x) (syn_clnqord R C) (.cv x)) (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R))) (syn_wbr (.cv u) R (.cv u)) p0034 p0069
  have p0071 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wbr (.cv x) (syn_clnqord R C) (.cv x)) (syn_wbr (.cv u) R (.cv u)) p0025 p0070
  have p0072 :=
    @g_rexlimddv (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) (syn_wbr (.cv x) (syn_clnqord R C) (.cv x)) u C dv_cache_0007 dv_cache_0008 p0010 p0071
  have p0073 :=
    @g_refrd (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) x (syn_clnquo R C) (syn_clnqord R C) (syn_cvv) (syn_cvv) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0002 p0005 p0072
  exact p0073

#print axioms g_lnqordref

end NFChoice.DirectNominalPrf.WPPReplay
