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
import NominalWPPReplayChunk015Compact001Part025

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

noncomputable def g_ellntpcndv
    (A : Class) (D : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) (hyp_ellntpcndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_ellntpcndv_2 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_ellntpcndv_3 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop R D) (syn_clntpc A)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D))) (.classEq D A))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((syn_cop R D)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, fresh_u_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_wb (.classMem (syn_cop R D) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (syn_cop R D)) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwrels, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, fresh_u_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_clntpc] using (Nominal.classEqRefl (syn_clntpc A)))
  have p0001 :=
    @g_eleq2i (syn_clntpc A) (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn A))) (syn_cop R D) p0000
  have p0002 :=
    @g_elin (syn_cop R D) (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn A))
  have p0003 :=
    @g_elin (syn_cop R D) (syn_clntp) (syn_chwrels)
  have p0004 :=
    (by simpa [syn_clntp] using (Nominal.classEqRefl (syn_clntp)))
  have p0005 :=
    @g_eleq2i (syn_clntp) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)) (syn_cop R D) p0004
  have p0006 :=
    @g_elin (syn_cop R D) (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)
  have p0007 :=
    @g_elin (syn_cop R D) (syn_cref) (syn_ctrans)
  have p0008 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr R (syn_cref) D)))
  have p0009 :=
    @g_bicomi (syn_wbr R (syn_cref) D) (.classMem (syn_cop R D) (syn_cref)) p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr R (syn_ctrans) D)))
  have p0011 :=
    @g_bicomi (syn_wbr R (syn_ctrans) D) (.classMem (syn_cop R D) (syn_ctrans)) p0010
  have p0012 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_cref)) (syn_wbr R (syn_cref) D) (.classMem (syn_cop R D) (syn_ctrans)) (syn_wbr R (syn_ctrans) D) p0009 p0011
  have p0013 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cin (syn_cref) (syn_ctrans))) (syn_wa (.classMem (syn_cop R D) (syn_cref)) (.classMem (syn_cop R D) (syn_ctrans))) (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) p0007 p0012
  have p0014 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr R (syn_cconnex) D)))
  have p0015 :=
    @g_bicomi (syn_wbr R (syn_cconnex) D) (.classMem (syn_cop R D) (syn_cconnex)) p0014
  have p0016 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_cin (syn_cref) (syn_ctrans))) (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) (.classMem (syn_cop R D) (syn_cconnex)) (syn_wbr R (syn_cconnex) D) p0013 p0015
  have p0017 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex))) (syn_wa (.classMem (syn_cop R D) (syn_cin (syn_cref) (syn_ctrans))) (.classMem (syn_cop R D) (syn_cconnex))) (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) (syn_wbr R (syn_cconnex) D)) p0006 p0016
  have p0018 :=
    @g_bitri (.classMem (syn_cop R D) (syn_clntp)) (.classMem (syn_cop R D) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex))) (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) (syn_wbr R (syn_cconnex) D)) p0005 p0017
  have p0019 :=
    @g_opex R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0020 :=
    @g_eleq1 (.cv u) (syn_cop R D) (syn_chwrels)
  have p0021 :=
    @g_fveq2 (.cv u) (syn_cop R D) (syn_c1st)
  have p0022 :=
    @g_fveq2 (.cv u) (syn_cop R D) (syn_c2nd)
  have p0023 :=
    @g_fveq2 (.cv u) (syn_cop R D) (syn_c2nd)
  have p0024 :=
    @g_xpeq12d (.classEq (.cv u) (syn_cop R D)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_cop R D)) p0022 p0023
  have p0025 :=
    @g_sseq12d (.classEq (.cv u) (syn_cop R D)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_cop R D)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D))) p0021 p0024
  have p0026 :=
    @g_bibi12d (.classEq (.cv u) (syn_cop R D)) (.classMem (.cv u) (syn_chwrels)) (.classMem (syn_cop R D) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (syn_cop R D)) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D)))) p0020 p0025
  have p0027 :=
    @g_elhwrrels u
  have p0028 :=
    @g_vtoclg (syn_wb (.classMem (.cv u) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wb (.classMem (syn_cop R D) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (syn_cop R D)) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D))))) u (syn_cop R D) (syn_cvv) dv_cache_0001 dv_cache_0002 p0026 p0027
  have p0029 :=
    Nominal.mp p0019 p0028
  have p0030 :=
    @g_opfv1st R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0031 :=
    @g_opfv2nd R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0032 :=
    @g_opfv2nd R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0033 :=
    @g_xpeq12i (syn_cfv (syn_c2nd) (syn_cop R D)) D (syn_cfv (syn_c2nd) (syn_cop R D)) D p0031 p0032
  have p0034 :=
    @g_sseq12i (syn_cfv (syn_c1st) (syn_cop R D)) R (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D))) (syn_cxp D D) p0030 p0033
  have p0035 :=
    @g_bitri (.classMem (syn_cop R D) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (syn_cop R D)) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D)))) (syn_wss R (syn_cxp D D)) p0029 p0034
  have p0036 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_clntp)) (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) (syn_wbr R (syn_cconnex) D)) (.classMem (syn_cop R D) (syn_chwrels)) (syn_wss R (syn_cxp D D)) p0018 p0035
  have p0037 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cin (syn_clntp) (syn_chwrels))) (syn_wa (.classMem (syn_cop R D) (syn_clntp)) (.classMem (syn_cop R D) (syn_chwrels))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D))) p0003 p0036
  have p0038 :=
    @g_opelxp R D (syn_cvv) (syn_csn A)
  have p0039 :=
    @g_biantrur (.classMem R (syn_cvv)) (.classMem D (syn_csn A)) hyp_ellntpcndv_2
  have p0040 :=
    @g_bicomi (.classMem D (syn_csn A)) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_csn A))) p0039
  have p0041 :=
    @g_elsnc2 D A hyp_ellntpcndv_1
  have p0042 :=
    @g_bitri (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_csn A))) (.classMem D (syn_csn A)) (.classEq D A) p0040 p0041
  have p0043 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_csn A))) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_csn A))) (.classEq D A) p0038 p0042
  have p0044 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_cin (syn_clntp) (syn_chwrels))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D))) (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_csn A))) (.classEq D A) p0037 p0043
  have p0045 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn A)))) (syn_wa (.classMem (syn_cop R D) (syn_cin (syn_clntp) (syn_chwrels))) (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_csn A)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D))) (.classEq D A)) p0002 p0044
  have p0046 :=
    @g_bitri (.classMem (syn_cop R D) (syn_clntpc A)) (.classMem (syn_cop R D) (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn A)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D))) (.classEq D A)) p0001 p0045
  exact p0046

noncomputable def g_ellnpwcndv
    (A : Class) (D : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) (hyp_ellnpwcndv_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_ellnpwcndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop R D) (syn_clnpwc A)) (syn_wa (.classMem (syn_cop R D) (syn_clntpc A)) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv
  let r : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_r_ne_d : r ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_r : d ≠ r :=
    Ne.symm fresh_r_ne_d
  have dv_cache_0001 : d ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ≠ r := by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have dv_cache_0004 : r ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : d ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : r ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ d from (by exact fresh_r_ne_d))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lnpwc A r d dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eleq2i (syn_clnpwc A) (syn_cin (syn_clntpc A) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))) (syn_cop R D) p0000
  have p0002 :=
    @g_elin (syn_cop R D) (syn_clntpc A) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))
  have p0003 :=
    @g_id (.classEq (.cv r) R)
  have p0004 :=
    @g_id (.classEq (.cv r) R)
  have p0005 :=
    @g_cnveqd (.classEq (.cv r) R) (.cv r) R p0004
  have p0006 :=
    @g_difeq12d (.classEq (.cv r) R) (.cv r) R (syn_ccnv (.cv r)) (syn_ccnv R) p0003 p0005
  have p0007 :=
    @g_breq1d (.classEq (.cv r) R) (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cdif R (syn_ccnv R)) (.cv d) (syn_cfound) p0006
  have p0008 :=
    @g_breq2 (.cv d) D (syn_cdif R (syn_ccnv R)) (syn_cfound)
  have p0009 :=
    @g_opelopabg (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) (.cv d)) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D) r d R D (syn_cvv) (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0007 p0008
  have p0010 :=
    @g_mp2an (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) (syn_wb (.classMem (syn_cop R D) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D)) hyp_ellnpwcndv_1 hyp_ellnpwcndv_2 p0009
  have p0011 :=
    @g_anbi2i (.classMem (syn_cop R D) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D) (.classMem (syn_cop R D) (syn_clntpc A)) p0010
  have p0012 :=
    @g_n_3bitri (.classMem (syn_cop R D) (syn_clnpwc A)) (.classMem (syn_cop R D) (syn_cin (syn_clntpc A) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))) (syn_wa (.classMem (syn_cop R D) (syn_clntpc A)) (.classMem (syn_cop R D) (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))) (syn_wa (.classMem (syn_cop R D) (syn_clntpc A)) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D)) p0001 p0002 p0011
  exact p0012

noncomputable def g_lnpwkerfnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnpwkerfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_fnlndifop
  have p0001 :=
    @g_ln1stfn
  have p0002 :=
    @g_lnpwasymfnfn
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnpwasymfn) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnpwasymfn)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_inidm (syn_cvv)
  have p0007 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) p0006
  have p0008 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cvv)) p0005 p0007
  have p0009 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) p0000 p0008
  have p0010 :=
    (by simpa [syn_clnpwkerfn] using (Nominal.classEqRefl (syn_clnpwkerfn)))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clnpwkerfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clnpwkerfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) (syn_cvv)) p0009 p0011
  exact p0012

noncomputable def g_lnpwkerfnex
     :
    Nominal.NPrf (.classMem (syn_clnpwkerfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnpwkerfn] using (Nominal.classEqRefl (syn_clnpwkerfn)))
  have p0001 :=
    @g_lndifopex
  have p0002 :=
    @g_n_1stex
  have p0003 :=
    @g_lnpwasymfnex
  have p0004 :=
    @g_txpex (syn_c1st) (syn_clnpwasymfn) p0002 p0003
  have p0005 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) p0001 p0004
  have p0006 :=
    @g_eqeltri (syn_clnpwkerfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_lnpwkerfnval
    (D : Class) (R : Class) (hyp_lnpwkerfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwkerfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwkerfn) (syn_cop R D)) (syn_clnker R)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_clnpwkerfn] using (Nominal.classEqRefl (syn_clnpwkerfn)))
  have p0001 :=
    @g_fveq1i (syn_cop R D) (syn_clnpwkerfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) p0000
  have p0002 :=
    @g_ln1stfn
  have p0003 :=
    @g_lnpwasymfnfn
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnpwasymfn) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnpwasymfn)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_inidm (syn_cvv)
  have p0008 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) p0007
  have p0009 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cvv)) p0006 p0008
  have p0010 :=
    @g_opex R D hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0011 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cvv)) (.classMem (syn_cop R D) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_fvco2 (syn_cvv) (syn_cop R D) (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_eqtri (syn_cfv (syn_clnpwkerfn) (syn_cop R D)) (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) (syn_cop R D)) (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cop R D))) p0001 p0013
  have p0015 :=
    @g_ln1stfn
  have p0016 :=
    @g_lnpwasymfnfn
  have p0017 :=
    @g_opex R D hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0018 :=
    @g_fvtxpvv (syn_cop R D) (syn_c1st) (syn_clnpwasymfn) p0015 p0016 p0017
  have p0019 :=
    @g_opfv1st R D hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0020 :=
    @g_lnpwasymfnval D R hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0021 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop R D)) R (syn_cfv (syn_clnpwasymfn) (syn_cop R D)) (syn_cdif R (syn_ccnv R)) p0019 p0020
  have p0022 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cop R D)) (syn_cop (syn_cfv (syn_c1st) (syn_cop R D)) (syn_cfv (syn_clnpwasymfn) (syn_cop R D))) (syn_cop R (syn_cdif R (syn_ccnv R))) p0018 p0021
  have p0023 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cop R D)) (syn_cop R (syn_cdif R (syn_ccnv R))) (syn_clndifop) p0022
  have p0024 :=
    @g_eqtri (syn_cfv (syn_clnpwkerfn) (syn_cop R D)) (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cop R D))) (syn_cfv (syn_clndifop) (syn_cop R (syn_cdif R (syn_ccnv R)))) p0014 p0023
  have p0025 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co R (syn_clndifop) (syn_cdif R (syn_ccnv R)))))
  have p0026 :=
    @g_eqcomi (syn_co R (syn_clndifop) (syn_cdif R (syn_ccnv R))) (syn_cfv (syn_clndifop) (syn_cop R (syn_cdif R (syn_ccnv R)))) p0025
  have p0027 :=
    @g_cnvex R hyp_lnpwkerfnval_1
  have p0028 :=
    @g_difex R (syn_ccnv R) hyp_lnpwkerfnval_1 p0027
  have p0029 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem (syn_cdif R (syn_ccnv R)) (syn_cvv)) hyp_lnpwkerfnval_1 p0028
  have p0030 :=
    @g_lndifopvalg R (syn_cdif R (syn_ccnv R)) (syn_cvv) (syn_cvv)
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop R (syn_cdif R (syn_ccnv R)))) (syn_co R (syn_clndifop) (syn_cdif R (syn_ccnv R))) (syn_cdif R (syn_cdif R (syn_ccnv R))) p0026 p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_clnpwkerfn) (syn_cop R D)) (syn_cfv (syn_clndifop) (syn_cop R (syn_cdif R (syn_ccnv R)))) (syn_cdif R (syn_cdif R (syn_ccnv R))) p0024 p0032
  have p0034 :=
    (by simpa [syn_clnker] using (Nominal.classEqRefl (syn_clnker R)))
  have p0035 :=
    @g_dfin4 R (syn_ccnv R)
  have p0036 :=
    @g_eqtri (syn_clnker R) (syn_cin R (syn_ccnv R)) (syn_cdif R (syn_cdif R (syn_ccnv R))) p0034 p0035
  have p0037 :=
    @g_eqcomi (syn_clnker R) (syn_cdif R (syn_cdif R (syn_ccnv R))) p0036
  have p0038 :=
    @g_eqtri (syn_cfv (syn_clnpwkerfn) (syn_cop R D)) (syn_cdif R (syn_cdif R (syn_ccnv R))) (syn_clnker R) p0033 p0037
  exact p0038

noncomputable def g_lninteropfn
     :
    Nominal.NPrf (syn_wfn (syn_clninterop) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_fnlndifop
  have p0001 :=
    @g_ln1stfn
  have p0002 :=
    @g_fnlndifop
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_inidm (syn_cvv)
  have p0007 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop)) p0006
  have p0008 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0005 p0007
  have p0009 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0000 p0008
  have p0010 :=
    (by simpa [syn_clninterop] using (Nominal.classEqRefl (syn_clninterop)))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clninterop) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clninterop) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv)) p0009 p0011
  exact p0012

noncomputable def g_lninteropex
     :
    Nominal.NPrf (.classMem (syn_clninterop) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clninterop] using (Nominal.classEqRefl (syn_clninterop)))
  have p0001 :=
    @g_lndifopex
  have p0002 :=
    @g_n_1stex
  have p0003 :=
    @g_lndifopex
  have p0004 :=
    @g_txpex (syn_c1st) (syn_clndifop) p0002 p0003
  have p0005 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0001 p0004
  have p0006 :=
    @g_eqeltri (syn_clninterop) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_lninteropval
    (A : Class) (B : Class) (hyp_lninteropval_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_lninteropval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clninterop) (syn_cop A B)) (syn_cin A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_clninterop] using (Nominal.classEqRefl (syn_clninterop)))
  have p0001 :=
    @g_fveq1i (syn_cop A B) (syn_clninterop) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0000
  have p0002 :=
    @g_ln1stfn
  have p0003 :=
    @g_fnlndifop
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_inidm (syn_cvv)
  have p0008 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop)) p0007
  have p0009 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0006 p0008
  have p0010 :=
    @g_opex A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0011 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) (.classMem (syn_cop A B) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_fvco2 (syn_cvv) (syn_cop A B) (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cop A B)) (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cop A B)) (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cop A B))) p0001 p0013
  have p0015 :=
    @g_ln1stfn
  have p0016 :=
    @g_fnlndifop
  have p0017 :=
    @g_opex A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0018 :=
    @g_fvtxpvv (syn_cop A B) (syn_c1st) (syn_clndifop) p0015 p0016 p0017
  have p0019 :=
    @g_opfv1st A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0020 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co A (syn_clndifop) B)))
  have p0021 :=
    @g_eqcomi (syn_co A (syn_clndifop) B) (syn_cfv (syn_clndifop) (syn_cop A B)) p0020
  have p0022 :=
    @g_pm3_2i (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) hyp_lninteropval_1 hyp_lninteropval_2
  have p0023 :=
    @g_lndifopvalg A B (syn_cvv) (syn_cvv)
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop A B)) (syn_co A (syn_clndifop) B) (syn_cdif A B) p0021 p0024
  have p0026 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop A B)) A (syn_cfv (syn_clndifop) (syn_cop A B)) (syn_cdif A B) p0019 p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cop A B)) (syn_cop (syn_cfv (syn_c1st) (syn_cop A B)) (syn_cfv (syn_clndifop) (syn_cop A B))) (syn_cop A (syn_cdif A B)) p0018 p0026
  have p0028 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cop A B)) (syn_cop A (syn_cdif A B)) (syn_clndifop) p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cop A B)) (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cop A B))) (syn_cfv (syn_clndifop) (syn_cop A (syn_cdif A B))) p0014 p0028
  have p0030 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co A (syn_clndifop) (syn_cdif A B))))
  have p0031 :=
    @g_eqcomi (syn_co A (syn_clndifop) (syn_cdif A B)) (syn_cfv (syn_clndifop) (syn_cop A (syn_cdif A B))) p0030
  have p0032 :=
    @g_difex A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0033 :=
    @g_pm3_2i (.classMem A (syn_cvv)) (.classMem (syn_cdif A B) (syn_cvv)) hyp_lninteropval_1 p0032
  have p0034 :=
    @g_lndifopvalg A (syn_cdif A B) (syn_cvv) (syn_cvv)
  have p0035 :=
    Nominal.mp p0033 p0034
  have p0036 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop A (syn_cdif A B))) (syn_co A (syn_clndifop) (syn_cdif A B)) (syn_cdif A (syn_cdif A B)) p0031 p0035
  have p0037 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cop A B)) (syn_cfv (syn_clndifop) (syn_cop A (syn_cdif A B))) (syn_cdif A (syn_cdif A B)) p0029 p0036
  have p0038 :=
    @g_dfin4 A B
  have p0039 :=
    @g_eqcomi (syn_cin A B) (syn_cdif A (syn_cdif A B)) p0038
  have p0040 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cop A B)) (syn_cdif A (syn_cdif A B)) (syn_cin A B) p0037 p0039
  exact p0040

noncomputable def g_lnimagecrossfnval
    (B : Class) (R : Class) (hyp_lnimagecrossfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnimagecrossfnval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnimagecrossfn) (syn_cop R B)) (syn_cxp B (syn_cvv))) := by
  let proofSupport : Finset Var := B.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_clnimagecrossfn] using (Nominal.classEqRefl (syn_clnimagecrossfn)))
  have p0001 :=
    @g_fveq1i (syn_cop R B) (syn_clnimagecrossfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) p0000
  have p0002 :=
    @g_ln2ndfn
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_inidm (syn_cvv)
  have p0010 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0009
  have p0011 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_opex R B hyp_lnimagecrossfnval_1 hyp_lnimagecrossfnval_2
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv)) (.classMem (syn_cop R B) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_fvco2 (syn_cvv) (syn_cop R B) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_clnimagecrossfn) (syn_cop R B)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cop R B)) (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cop R B))) p0001 p0015
  have p0017 :=
    @g_ln2ndfn
  have p0018 :=
    @g_vvex
  have p0019 :=
    @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_opex R B hyp_lnimagecrossfnval_1 hyp_lnimagecrossfnval_2
  have p0022 :=
    @g_fvtxpvv (syn_cop R B) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) p0017 p0020 p0021
  have p0023 :=
    @g_opfv2nd R B hyp_lnimagecrossfnval_1 hyp_lnimagecrossfnval_2
  have p0024 :=
    @g_opex R B hyp_lnimagecrossfnval_1 hyp_lnimagecrossfnval_2
  have p0025 :=
    @g_vvex
  have p0026 :=
    @g_fvconst2 (syn_cvv) (syn_cvv) (syn_cop R B) p0025
  have p0027 :=
    Nominal.mp p0024 p0026
  have p0028 :=
    @g_opeq12i (syn_cfv (syn_c2nd) (syn_cop R B)) B (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cop R B)) (syn_cvv) p0023 p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cop R B)) (syn_cop (syn_cfv (syn_c2nd) (syn_cop R B)) (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cop R B))) (syn_cop B (syn_cvv)) p0022 p0028
  have p0030 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cop R B)) (syn_cop B (syn_cvv)) (syn_ccross) p0029
  have p0031 :=
    @g_eqtri (syn_cfv (syn_clnimagecrossfn) (syn_cop R B)) (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cop R B))) (syn_cfv (syn_ccross) (syn_cop B (syn_cvv))) p0016 p0030
  have p0032 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co B (syn_ccross) (syn_cvv))))
  have p0033 :=
    @g_eqcomi (syn_co B (syn_ccross) (syn_cvv)) (syn_cfv (syn_ccross) (syn_cop B (syn_cvv))) p0032
  have p0034 :=
    @g_vvex
  have p0035 :=
    @g_pm3_2i (.classMem B (syn_cvv)) (.classMem (syn_cvv) (syn_cvv)) hyp_lnimagecrossfnval_2 p0034
  have p0036 :=
    @g_ovcross B (syn_cvv) (syn_cvv) (syn_cvv)
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_eqtri (syn_cfv (syn_ccross) (syn_cop B (syn_cvv))) (syn_co B (syn_ccross) (syn_cvv)) (syn_cxp B (syn_cvv)) p0033 p0037
  have p0039 :=
    @g_eqtri (syn_cfv (syn_clnimagecrossfn) (syn_cop R B)) (syn_cfv (syn_ccross) (syn_cop B (syn_cvv))) (syn_cxp B (syn_cvv)) p0031 p0038
  exact p0039

noncomputable def g_lnimageresfnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnimageresfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_fnlndifop
  have p0001 :=
    @g_ln1stfn
  have p0002 :=
    @g_fnlndifop
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_inidm (syn_cvv)
  have p0007 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop)) p0006
  have p0008 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0005 p0007
  have p0009 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0000 p0008
  have p0010 :=
    (by simpa [syn_clninterop] using (Nominal.classEqRefl (syn_clninterop)))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clninterop) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clninterop) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv)) p0009 p0011
  have p0013 :=
    @g_ln1stfn
  have p0014 :=
    @g_fncross
  have p0015 :=
    @g_ln2ndfn
  have p0016 :=
    @g_vvex
  have p0017 :=
    @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0015 p0018
  have p0020 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_inidm (syn_cvv)
  have p0023 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0022
  have p0024 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv)) p0021 p0023
  have p0025 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0014 p0024
  have p0026 :=
    (by simpa [syn_clnimagecrossfn] using (Nominal.classEqRefl (syn_clnimagecrossfn)))
  have p0027 :=
    @g_fneq1i (syn_cvv) (syn_clnimagecrossfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) p0026
  have p0028 :=
    @g_mpbir (syn_wfn (syn_clnimagecrossfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv)) p0025 p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnimagecrossfn) (syn_cvv)) p0013 p0028
  have p0030 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnimagecrossfn)
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    @g_inidm (syn_cvv)
  have p0033 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0032
  have p0034 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv)) p0031 p0033
  have p0035 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0012 p0034
  have p0036 :=
    (by simpa [syn_clnimageresfn] using (Nominal.classEqRefl (syn_clnimageresfn)))
  have p0037 :=
    @g_fneq1i (syn_cvv) (syn_clnimageresfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) p0036
  have p0038 :=
    @g_mpbir (syn_wfn (syn_clnimageresfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) (syn_cvv)) p0035 p0037
  exact p0038

noncomputable def g_lnimageresfnex
     :
    Nominal.NPrf (.classMem (syn_clnimageresfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnimageresfn] using (Nominal.classEqRefl (syn_clnimageresfn)))
  have p0001 :=
    (by simpa [syn_clninterop] using (Nominal.classEqRefl (syn_clninterop)))
  have p0002 :=
    @g_lndifopex
  have p0003 :=
    @g_n_1stex
  have p0004 :=
    @g_lndifopex
  have p0005 :=
    @g_txpex (syn_c1st) (syn_clndifop) p0003 p0004
  have p0006 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0002 p0005
  have p0007 :=
    @g_eqeltri (syn_clninterop) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv) p0001 p0006
  have p0008 :=
    @g_n_1stex
  have p0009 :=
    (by simpa [syn_clnimagecrossfn] using (Nominal.classEqRefl (syn_clnimagecrossfn)))
  have p0010 :=
    @g_crossex
  have p0011 :=
    @g_n_2ndex
  have p0012 :=
    @g_vvex
  have p0013 :=
    @g_snex (syn_cvv)
  have p0014 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_txpex (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) p0011 p0014
  have p0016 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0010 p0015
  have p0017 :=
    @g_eqeltri (syn_clnimagecrossfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv) p0009 p0016
  have p0018 :=
    @g_txpex (syn_c1st) (syn_clnimagecrossfn) p0008 p0017
  have p0019 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0007 p0018
  have p0020 :=
    @g_eqeltri (syn_clnimageresfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) (syn_cvv) p0000 p0019
  exact p0020

noncomputable def g_lnimageresfnval
    (B : Class) (R : Class) (hyp_lnimageresfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnimageresfnval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnimageresfn) (syn_cop R B)) (syn_cres R B)) := by
  let proofSupport : Finset Var := B.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_clnimageresfn] using (Nominal.classEqRefl (syn_clnimageresfn)))
  have p0001 :=
    @g_fveq1i (syn_cop R B) (syn_clnimageresfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) p0000
  have p0002 :=
    @g_ln1stfn
  have p0003 :=
    @g_fncross
  have p0004 :=
    @g_ln2ndfn
  have p0005 :=
    @g_vvex
  have p0006 :=
    @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0004 p0007
  have p0009 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_inidm (syn_cvv)
  have p0012 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0011
  have p0013 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0003 p0013
  have p0015 :=
    (by simpa [syn_clnimagecrossfn] using (Nominal.classEqRefl (syn_clnimagecrossfn)))
  have p0016 :=
    @g_fneq1i (syn_cvv) (syn_clnimagecrossfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) p0015
  have p0017 :=
    @g_mpbir (syn_wfn (syn_clnimagecrossfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv)) p0014 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnimagecrossfn) (syn_cvv)) p0002 p0017
  have p0019 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnimagecrossfn)
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_inidm (syn_cvv)
  have p0022 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0021
  have p0023 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv)) p0020 p0022
  have p0024 :=
    @g_opex R B hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0025 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv)) (.classMem (syn_cop R B) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_fvco2 (syn_cvv) (syn_cop R B) (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_eqtri (syn_cfv (syn_clnimageresfn) (syn_cop R B)) (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) (syn_cop R B)) (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cop R B))) p0001 p0027
  have p0029 :=
    @g_ln1stfn
  have p0030 :=
    @g_fncross
  have p0031 :=
    @g_ln2ndfn
  have p0032 :=
    @g_vvex
  have p0033 :=
    @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0031 p0034
  have p0036 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_inidm (syn_cvv)
  have p0039 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0038
  have p0040 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv)) p0037 p0039
  have p0041 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0030 p0040
  have p0042 :=
    (by simpa [syn_clnimagecrossfn] using (Nominal.classEqRefl (syn_clnimagecrossfn)))
  have p0043 :=
    @g_fneq1i (syn_cvv) (syn_clnimagecrossfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) p0042
  have p0044 :=
    @g_mpbir (syn_wfn (syn_clnimagecrossfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv)) p0041 p0043
  have p0045 :=
    @g_opex R B hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0046 :=
    @g_fvtxpvv (syn_cop R B) (syn_c1st) (syn_clnimagecrossfn) p0029 p0044 p0045
  have p0047 :=
    @g_opfv1st R B hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0048 :=
    @g_lnimagecrossfnval B R hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0049 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop R B)) R (syn_cfv (syn_clnimagecrossfn) (syn_cop R B)) (syn_cxp B (syn_cvv)) p0047 p0048
  have p0050 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cop R B)) (syn_cop (syn_cfv (syn_c1st) (syn_cop R B)) (syn_cfv (syn_clnimagecrossfn) (syn_cop R B))) (syn_cop R (syn_cxp B (syn_cvv))) p0046 p0049
  have p0051 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cop R B)) (syn_cop R (syn_cxp B (syn_cvv))) (syn_clninterop) p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_clnimageresfn) (syn_cop R B)) (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cop R B))) (syn_cfv (syn_clninterop) (syn_cop R (syn_cxp B (syn_cvv)))) p0028 p0051
  have p0053 :=
    @g_vvex
  have p0054 :=
    @g_xpex B (syn_cvv) hyp_lnimageresfnval_2 p0053
  have p0055 :=
    @g_lninteropval R (syn_cxp B (syn_cvv)) hyp_lnimageresfnval_1 p0054
  have p0056 :=
    @g_eqtri (syn_cfv (syn_clnimageresfn) (syn_cop R B)) (syn_cfv (syn_clninterop) (syn_cop R (syn_cxp B (syn_cvv)))) (syn_cin R (syn_cxp B (syn_cvv))) p0052 p0055
  have p0057 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres R B)))
  have p0058 :=
    @g_eqcomi (syn_cres R B) (syn_cin R (syn_cxp B (syn_cvv))) p0057
  have p0059 :=
    @g_eqtri (syn_cfv (syn_clnimageresfn) (syn_cop R B)) (syn_cin R (syn_cxp B (syn_cvv))) (syn_cres R B) p0056 p0058
  exact p0059

noncomputable def g_lnimageopfn
     :
    Nominal.NPrf (syn_wfn (syn_clnimageop) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_ranfnfn
  have p0001 :=
    @g_fnlndifop
  have p0002 :=
    @g_ln1stfn
  have p0003 :=
    @g_fnlndifop
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_inidm (syn_cvv)
  have p0008 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop)) p0007
  have p0009 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0006 p0008
  have p0010 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0001 p0009
  have p0011 :=
    (by simpa [syn_clninterop] using (Nominal.classEqRefl (syn_clninterop)))
  have p0012 :=
    @g_fneq1i (syn_cvv) (syn_clninterop) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0011
  have p0013 :=
    @g_mpbir (syn_wfn (syn_clninterop) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_ln1stfn
  have p0015 :=
    @g_fncross
  have p0016 :=
    @g_ln2ndfn
  have p0017 :=
    @g_vvex
  have p0018 :=
    @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0016 p0019
  have p0021 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_inidm (syn_cvv)
  have p0024 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0023
  have p0025 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv)) p0022 p0024
  have p0026 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0015 p0025
  have p0027 :=
    (by simpa [syn_clnimagecrossfn] using (Nominal.classEqRefl (syn_clnimagecrossfn)))
  have p0028 :=
    @g_fneq1i (syn_cvv) (syn_clnimagecrossfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) p0027
  have p0029 :=
    @g_mpbir (syn_wfn (syn_clnimagecrossfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv)) p0026 p0028
  have p0030 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnimagecrossfn) (syn_cvv)) p0014 p0029
  have p0031 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnimagecrossfn)
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_inidm (syn_cvv)
  have p0034 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0033
  have p0035 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv)) p0032 p0034
  have p0036 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0013 p0035
  have p0037 :=
    (by simpa [syn_clnimageresfn] using (Nominal.classEqRefl (syn_clnimageresfn)))
  have p0038 :=
    @g_fneq1i (syn_cvv) (syn_clnimageresfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) p0037
  have p0039 :=
    @g_mpbir (syn_wfn (syn_clnimageresfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) (syn_cvv)) p0036 p0038
  have p0040 :=
    @g_fncovv (syn_cranfn) (syn_clnimageresfn) p0000 p0039
  have p0041 :=
    (by simpa [syn_clnimageop] using (Nominal.classEqRefl (syn_clnimageop)))
  have p0042 :=
    @g_fneq1i (syn_cvv) (syn_clnimageop) (syn_ccom (syn_cranfn) (syn_clnimageresfn)) p0041
  have p0043 :=
    @g_mpbir (syn_wfn (syn_clnimageop) (syn_cvv)) (syn_wfn (syn_ccom (syn_cranfn) (syn_clnimageresfn)) (syn_cvv)) p0040 p0042
  exact p0043

noncomputable def g_lnimageopex
     :
    Nominal.NPrf (.classMem (syn_clnimageop) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnimageop] using (Nominal.classEqRefl (syn_clnimageop)))
  have p0001 :=
    @g_ranfnex
  have p0002 :=
    (by simpa [syn_clnimageresfn] using (Nominal.classEqRefl (syn_clnimageresfn)))
  have p0003 :=
    (by simpa [syn_clninterop] using (Nominal.classEqRefl (syn_clninterop)))
  have p0004 :=
    @g_lndifopex
  have p0005 :=
    @g_n_1stex
  have p0006 :=
    @g_lndifopex
  have p0007 :=
    @g_txpex (syn_c1st) (syn_clndifop) p0005 p0006
  have p0008 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0004 p0007
  have p0009 :=
    @g_eqeltri (syn_clninterop) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv) p0003 p0008
  have p0010 :=
    @g_n_1stex
  have p0011 :=
    (by simpa [syn_clnimagecrossfn] using (Nominal.classEqRefl (syn_clnimagecrossfn)))
  have p0012 :=
    @g_crossex
  have p0013 :=
    @g_n_2ndex
  have p0014 :=
    @g_vvex
  have p0015 :=
    @g_snex (syn_cvv)
  have p0016 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_txpex (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) p0013 p0016
  have p0018 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0012 p0017
  have p0019 :=
    @g_eqeltri (syn_clnimagecrossfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv) p0011 p0018
  have p0020 :=
    @g_txpex (syn_c1st) (syn_clnimagecrossfn) p0010 p0019
  have p0021 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0009 p0020
  have p0022 :=
    @g_eqeltri (syn_clnimageresfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) (syn_cvv) p0002 p0021
  have p0023 :=
    @g_coex (syn_cranfn) (syn_clnimageresfn) p0001 p0022
  have p0024 :=
    @g_eqeltri (syn_clnimageop) (syn_ccom (syn_cranfn) (syn_clnimageresfn)) (syn_cvv) p0000 p0023
  exact p0024

#print axioms g_lnimageopex

end NFChoice.DirectNominalPrf.WPPReplay
