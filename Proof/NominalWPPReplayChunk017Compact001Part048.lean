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
import NominalWPPReplayChunk017Compact001Part047

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

noncomputable def g_hncodecmplnpwcndv
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clnpwc (syn_chwcn A)))) := by
  let proofSupport : Finset Var := A.fv
  let r : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (h)
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (h)
  have fresh_r_ne_d : r ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_r : d ≠ r :=
    Ne.symm fresh_r_ne_d
  have dv_cache_0001 : r ∉ ((syn_cop (syn_chncodecmpset A) (syn_chwcn A))).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((Wff.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwrels, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_chncodecmpset A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((syn_chncodecmpset A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : d ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cfound) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cfound) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : r ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ d from (by exact fresh_r_ne_d))
  have dv_cache_0011 : d ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have p0000 :=
    @g_hncodecmpsetrefndv A
  have p0001 :=
    @g_hncodecmpsettransndv A
  have p0002 :=
    @g_jca (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0000 p0001
  have p0003 :=
    @g_hncodecmpsetconnexndv A
  have p0004 :=
    @g_jca (.classMem A (syn_cvv)) (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0002 p0003
  have p0005 :=
    (by simpa [syn_clntp] using (Nominal.classEqRefl (syn_clntp)))
  have p0006 :=
    @g_breqi (syn_chncodecmpset A) (syn_chwcn A) (syn_clntp) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)) p0005
  have p0007 :=
    @g_brin (syn_chncodecmpset A) (syn_chwcn A) (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)
  have p0008 :=
    @g_brin (syn_chncodecmpset A) (syn_chwcn A) (syn_cref) (syn_ctrans)
  have p0009 :=
    @g_anbi1i (syn_wbr (syn_chncodecmpset A) (syn_cin (syn_cref) (syn_ctrans)) (syn_chwcn A)) (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0008
  have p0010 :=
    @g_bitri (syn_wbr (syn_chncodecmpset A) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)) (syn_chwcn A)) (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cin (syn_cref) (syn_ctrans)) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A))) (syn_wa (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A))) p0007 p0009
  have p0011 :=
    @g_bitri (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)) (syn_chwcn A)) (syn_wa (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A))) p0006 p0010
  have p0012 :=
    @g_a1i (syn_wb (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A)) (syn_wa (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)))) (.classMem A (syn_cvv)) p0011
  have p0013 :=
    @g_mpbird (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A)) (syn_wa (syn_wa (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A))) p0004 p0012
  have p0014 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A))))
  have p0015 :=
    @g_biimpi (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp)) p0014
  have p0016 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_clntp) (syn_chwcn A)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp)) p0013 p0015
  have p0017 :=
    @g_hncodecmpsetssxpndv A
  have p0018 :=
    @g_a1i (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (.classMem A (syn_cvv)) p0017
  have p0019 :=
    @g_hncodecmpsetexg A
  have p0020 :=
    @g_hwcnexg A
  have p0021 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_opexg (syn_chncodecmpset A) (syn_chwcn A) (syn_cvv) (syn_cvv)
  have p0023 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cvv)) p0021 p0022
  have p0024 :=
    @g_eleq1 (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)
  have p0025 :=
    @g_fveq2 (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_c1st)
  have p0026 :=
    @g_fveq2 (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_c2nd)
  have p0027 :=
    @g_fveq2 (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_c2nd)
  have p0028 :=
    @g_xpeq12d (.classEq (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cfv (syn_c2nd) (.cv r)) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cfv (syn_c2nd) (.cv r)) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) p0026 p0027
  have p0029 :=
    @g_sseq12d (.classEq (.cv r) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cfv (syn_c1st) (.cv r)) (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cxp (syn_cfv (syn_c2nd) (.cv r)) (syn_cfv (syn_c2nd) (.cv r))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))) p0025 p0028
  have p0030 :=
    @g_elhwrrels r
  have p0031 :=
    @g_vtoclbg (.classMem (.cv r) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (.cv r)) (syn_cxp (syn_cfv (syn_c2nd) (.cv r)) (syn_cfv (syn_c2nd) (.cv r)))) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))))) r (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0024 p0029 p0030
  have p0032 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cvv)) (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))))) p0023 p0031
  have p0033 :=
    @g_hncodecmpsetexg A
  have p0034 :=
    @g_hwcnexg A
  have p0035 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0033 p0034
  have p0036 :=
    @g_opfvscl (syn_chncodecmpset A) (syn_chwcn A)
  have p0037 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chncodecmpset A)) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A))) p0035 p0036
  have p0038 :=
    @g_simpld (.classMem A (syn_cvv)) (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chncodecmpset A)) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A)) p0037
  have p0039 :=
    @g_hncodecmpsetexg A
  have p0040 :=
    @g_hwcnexg A
  have p0041 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0039 p0040
  have p0042 :=
    @g_opfvscl (syn_chncodecmpset A) (syn_chwcn A)
  have p0043 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chncodecmpset A)) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A))) p0041 p0042
  have p0044 :=
    @g_simprd (.classMem A (syn_cvv)) (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chncodecmpset A)) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A)) p0043
  have p0045 :=
    @g_hncodecmpsetexg A
  have p0046 :=
    @g_hwcnexg A
  have p0047 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0045 p0046
  have p0048 :=
    @g_opfvscl (syn_chncodecmpset A) (syn_chwcn A)
  have p0049 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chncodecmpset A)) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A))) p0047 p0048
  have p0050 :=
    @g_simprd (.classMem A (syn_cvv)) (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chncodecmpset A)) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A)) p0049
  have p0051 :=
    @g_xpeq12d (.classMem A (syn_cvv)) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chwcn A) p0044 p0050
  have p0052 :=
    @g_sseq12d (.classMem A (syn_cvv)) (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_chncodecmpset A) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)))) (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0038 p0051
  have p0053 :=
    @g_bitrd (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))) (syn_cfv (syn_c2nd) (syn_cop (syn_chncodecmpset A) (syn_chwcn A))))) (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0032 p0052
  have p0054 :=
    @g_mpbird (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)) (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0018 p0053
  have p0055 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)) p0016 p0054
  have p0056 :=
    @g_elin (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp) (syn_chwrels)
  have p0057 :=
    @g_a1i (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_clntp) (syn_chwrels))) (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels)))) (.classMem A (syn_cvv)) p0056
  have p0058 :=
    @g_mpbird (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_clntp) (syn_chwrels))) (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntp)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_chwrels))) p0055 p0057
  have p0059 :=
    @g_hncodecmpsetexg A
  have p0060 :=
    @g_hwcnexg A
  have p0061 :=
    @g_snidg (syn_chwcn A) (syn_cvv)
  have p0062 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_csn (syn_chwcn A))) p0060 p0061
  have p0063 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_csn (syn_chwcn A))) p0059 p0062
  have p0064 :=
    @g_opelxp (syn_chncodecmpset A) (syn_chwcn A) (syn_cvv) (syn_csn (syn_chwcn A))
  have p0065 :=
    @g_a1i (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))) (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_csn (syn_chwcn A))))) (.classMem A (syn_cvv)) p0064
  have p0066 :=
    @g_mpbird (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))) (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_csn (syn_chwcn A)))) p0063 p0065
  have p0067 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_clntp) (syn_chwrels))) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))) p0058 p0066
  have p0068 :=
    @g_elin (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))
  have p0069 :=
    @g_a1i (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))) (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_clntp) (syn_chwrels))) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))))) (.classMem A (syn_cvv)) p0068
  have p0070 :=
    @g_mpbird (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))) (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_clntp) (syn_chwrels))) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))) p0067 p0069
  have p0071 :=
    (by simpa [syn_clntpc] using (Nominal.classEqRefl (syn_clntpc (syn_chwcn A))))
  have p0072 :=
    @g_a1i (.classEq (syn_clntpc (syn_chwcn A)) (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A))))) (.classMem A (syn_cvv)) p0071
  have p0073 :=
    @g_eleqtrrd (.classMem A (syn_cvv)) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn (syn_chwcn A)))) (syn_clntpc (syn_chwcn A)) p0070 p0072
  have p0074 :=
    @g_hncodecmpstrictfrndv A
  have p0075 :=
    @g_hncodecmpsetexg A
  have p0076 :=
    @g_hwcnexg A
  have p0077 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0075 p0076
  have p0078 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A))
  have p0079 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A))
  have p0080 :=
    @g_cnveqd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A))) (.cv r) (syn_chncodecmpset A) p0079
  have p0081 :=
    @g_difeq12d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A))) (.cv r) (syn_chncodecmpset A) (syn_ccnv (.cv r)) (syn_ccnv (syn_chncodecmpset A)) p0078 p0080
  have p0082 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A))
  have p0083 :=
    @g_breq12d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv d) (syn_chwcn A))) (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv d) (syn_chwcn A) (syn_cfound) p0081 p0082
  have p0084 :=
    @g_opelopabga (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)) (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cfound) (syn_chwcn A)) r d (syn_chncodecmpset A) (syn_chwcn A) (syn_cvv) (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0083
  have p0085 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))) (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cfound) (syn_chwcn A))) p0077 p0084
  have p0086 :=
    @g_mpbird (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))) (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cfound) (syn_chwcn A)) p0074 p0085
  have p0087 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntpc (syn_chwcn A))) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))) p0073 p0086
  have p0088 :=
    @g_elin (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntpc (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))
  have p0089 :=
    @g_a1i (syn_wb (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_clntpc (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))) (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntpc (syn_chwcn A))) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))))) (.classMem A (syn_cvv)) p0088
  have p0090 :=
    @g_mpbird (.classMem A (syn_cvv)) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_clntpc (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))) (syn_wa (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_clntpc (syn_chwcn A))) (.classMem (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))) p0087 p0089
  have p0091 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lnpwc (syn_chwcn A) r d dv_cache_0007 dv_cache_0006 dv_cache_0011
  have p0092 :=
    @g_a1i (.classEq (syn_clnpwc (syn_chwcn A)) (syn_cin (syn_clntpc (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))) (.classMem A (syn_cvv)) p0091
  have p0093 :=
    @g_eleqtrrd (.classMem A (syn_cvv)) (syn_cop (syn_chncodecmpset A) (syn_chwcn A)) (syn_cin (syn_clntpc (syn_chwcn A)) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))) (syn_clnpwc (syn_chwcn A)) p0090 p0092
  exact p0093

noncomputable def g_hnordlnquoeqimndv
    (A : Class) (r : Var) (dv_A_r : r ∉ A.fv) :
    Nominal.NPrf (.imp (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) (.classEq (syn_clnquo (.cv r) (syn_chwcn A)) (syn_chnord A))) := by
  let proofSupport : Finset Var := A.fv ∪ ({r} : Finset Var)
  have p0000 :=
    (by simpa [syn_clnquo] using (Nominal.classEqRefl (syn_clnquo (.cv r) (syn_chwcn A))))
  have p0001 :=
    @g_a1i (.classEq (syn_clnquo (.cv r) (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker (.cv r)))) (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) p0000
  have p0002 :=
    @g_qseq2 (syn_clnker (.cv r)) (syn_chwniso A) (syn_chwcn A)
  have p0003 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0004 :=
    @g_eqcomi (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0003
  have p0005 :=
    @g_a1i (.classEq (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A)) (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) p0004
  have p0006 :=
    @g_n_3eqtrd (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) (syn_clnquo (.cv r) (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker (.cv r))) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A) p0001 p0002 p0005
  exact p0006

noncomputable def g_hnordwendv
    (A : Class) (s : Var) (dv_A_s : s ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))) := by
  let proofSupport : Finset Var := A.fv ∪ ({s} : Finset Var)
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_ne_s : r ≠ s := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_s_ne_r : s ≠ r :=
    Ne.symm fresh_r_ne_s
  have dv_cache_0001 : r ∉ ((syn_chncodecmpset A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({r} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show r ∉ (A).fv from (by exact fresh_r_not_A))))))
  have dv_cache_0003 : s ∉ ((syn_clnqord (.cv r) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_s, fresh_s_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_s, fresh_s_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : s ∉ ((syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_s, fresh_s_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_s, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hncodecmpsetexg A
  have p0001 :=
    @g_isset r (syn_chncodecmpset A) dv_cache_0001
  have p0002 :=
    @g_a1i (syn_wb (.classMem (syn_chncodecmpset A) (syn_cvv)) (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A)))) (.classMem A (syn_cvv)) p0001
  have p0003 :=
    @g_biimpd (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A))) p0002
  have p0004 :=
    @g_mpd (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A))) p0000 p0003
  have p0005 :=
    @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0006 :=
    @g_hncodecmpsetexg A
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0009 :=
    @g_eleq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.cv r) (syn_chncodecmpset A) (syn_cvv) p0008
  have p0010 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0007 p0009
  have p0011 :=
    @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0012 :=
    @g_hwcnexg A
  have p0013 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0010 p0013
  have p0015 :=
    @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0016 :=
    @g_hncodecmpsetrefndv A
  have p0017 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0015 p0016
  have p0018 :=
    @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0019 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cref) p0018
  have p0020 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0017 p0019
  have p0021 :=
    @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0022 :=
    @g_hncodecmpsettransndv A
  have p0023 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0021 p0022
  have p0024 :=
    @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0025 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_ctrans) p0024
  have p0026 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0023 p0025
  have p0027 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) p0020 p0026
  have p0028 :=
    @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0029 :=
    @g_hncodecmpsetconnexndv A
  have p0030 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0028 p0029
  have p0031 :=
    @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0032 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cconnex) p0031
  have p0033 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0030 p0032
  have p0034 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)) p0027 p0033
  have p0035 :=
    @g_hncodecmpsetssxpndv A
  have p0036 :=
    @g_a1i (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) p0035
  have p0037 :=
    @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0038 :=
    @g_sseq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.cv r) (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0037
  have p0039 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0036 p0038
  have p0040 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0034 p0039
  have p0041 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) p0014 p0040
  have p0042 :=
    @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0043 :=
    @g_hncodecmpstrictfrndv A
  have p0044 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem A (syn_cvv)) (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cfound) (syn_chwcn A)) p0042 p0043
  have p0045 :=
    @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0046 :=
    @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0047 :=
    @g_cnveqd (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.cv r) (syn_chncodecmpset A) p0046
  have p0048 :=
    @g_difeq12d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.cv r) (syn_chncodecmpset A) (syn_ccnv (.cv r)) (syn_ccnv (syn_chncodecmpset A)) p0045 p0047
  have p0049 :=
    @g_breq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_chwcn A) (syn_cfound) p0048
  have p0050 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (syn_chwcn A)) (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cfound) (syn_chwcn A)) p0044 p0049
  have p0051 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))) (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (syn_chwcn A)) p0041 p0050
  have p0052 :=
    @g_lnqordwe (syn_chwcn A) (.cv r) dv_cache_0002
  have p0053 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))) (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (syn_chwcn A))) (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_clnquo (.cv r) (syn_chwcn A))) p0051 p0052
  have p0054 :=
    @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0055 :=
    @g_lnkereq (.cv r) (syn_chncodecmpset A)
  have p0056 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A))) p0054 p0055
  have p0057 :=
    @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0058 :=
    @g_hncodecmplnkerndv A
  have p0059 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem A (syn_cvv)) (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0057 p0058
  have p0060 :=
    @g_eqtrd (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) p0056 p0059
  have p0061 :=
    (by simpa [syn_clnquo] using (Nominal.classEqRefl (syn_clnquo (.cv r) (syn_chwcn A))))
  have p0062 :=
    @g_a1i (.classEq (syn_clnquo (.cv r) (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker (.cv r)))) (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) p0061
  have p0063 :=
    @g_qseq2 (syn_clnker (.cv r)) (syn_chwniso A) (syn_chwcn A)
  have p0064 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0065 :=
    @g_eqcomi (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0064
  have p0066 :=
    @g_a1i (.classEq (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A)) (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) p0065
  have p0067 :=
    @g_n_3eqtrd (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) (syn_clnquo (.cv r) (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker (.cv r))) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A) p0062 p0063 p0066
  have p0068 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) (.classEq (syn_clnquo (.cv r) (syn_chwcn A)) (syn_chnord A)) p0060 p0067
  have p0069 :=
    @g_breq2d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_clnquo (.cv r) (syn_chwcn A)) (syn_chnord A) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) p0068
  have p0070 :=
    @g_mpbid (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_clnquo (.cv r) (syn_chwcn A))) (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) p0053 p0069
  have p0071 :=
    @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0072 :=
    @g_hncodecmpsetexg A
  have p0073 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0071 p0072
  have p0074 :=
    @g_simpr (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0075 :=
    @g_eleq1d (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.cv r) (syn_chncodecmpset A) (syn_cvv) p0074
  have p0076 :=
    @g_mpbird (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0073 p0075
  have p0077 :=
    @g_simpl (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))
  have p0078 :=
    @g_hwcnexg A
  have p0079 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0077 p0078
  have p0080 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0076 p0079
  have p0081 :=
    @g_lnqordexg (syn_chwcn A) (.cv r) dv_cache_0002
  have p0082 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv)) p0080 p0081
  have p0083 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))
  have p0084 :=
    @g_breq1d (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))) (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_chnord A) (syn_cwe) p0083
  have p0085 :=
    @g_biimprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))) (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) p0084
  have p0086 :=
    @g_spcimedv (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) s (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0082 p0085
  have p0087 :=
    @g_mpd (syn_wa (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A))) (syn_wbr (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cwe) (syn_chnord A)) (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))) p0070 p0086
  have p0088 :=
    @g_exlimddv (.classMem A (syn_cvv)) (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))) r dv_cache_0006 dv_cache_0007 p0004 p0087
  exact p0088

#print axioms g_hnordwendv

end NFChoice.DirectNominalPrf.WPPReplay
