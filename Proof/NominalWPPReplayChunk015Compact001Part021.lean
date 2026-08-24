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
import NominalWPPReplayChunk015Compact001Part020

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

noncomputable def g_hncardmono
    (A : Class) (D : Class) (hyp_hncardmono_1 : Nominal.NPrf (syn_wss D A)) (hyp_hncardmono_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hncardmono_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ ((syn_chnqinc D A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, fresh_f_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_chnord D)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((syn_chnord A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnqincf1 A D hyp_hncardmono_1 hyp_hncardmono_2 hyp_hncardmono_3
  have p0001 :=
    @g_pm3_2i (.classMem D (syn_cvv)) (.classMem A (syn_cvv)) hyp_hncardmono_2 hyp_hncardmono_3
  have p0002 :=
    @g_hnqincexg A D
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_f1eq1 (syn_chnord D) (syn_chnord A) (.cv f) (syn_chnqinc D A)
  have p0005 :=
    @g_spcegv (syn_wf1 (.cv f) (syn_chnord D) (syn_chnord A)) (syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) f (syn_chnqinc D A) (syn_cvv) dv_cache_0001 dv_cache_0002 p0004
  have p0006 :=
    Nominal.mp p0003 p0005
  have p0007 :=
    Nominal.mp p0000 p0006
  have p0008 :=
    @g_hnordex D hyp_hncardmono_2
  have p0009 :=
    @g_hnordex A hyp_hncardmono_3
  have p0010 :=
    @g_nclenc (syn_chnord D) (syn_chnord A) f dv_cache_0003 dv_cache_0004 p0008 p0009
  have p0011 :=
    @g_mpbir (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A))) (syn_wex f (syn_wf1 (.cv f) (syn_chnord D) (syn_chnord A))) p0007 p0010
  have p0012 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard D)))
  have p0013 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard A)))
  have p0014 :=
    @g_breq12i (syn_chncard D) (syn_cnc (syn_chnord D)) (syn_chncard A) (syn_cnc (syn_chnord A)) (syn_clec) p0012 p0013
  have p0015 :=
    @g_mpbir (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A)) (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A))) p0011 p0014
  exact p0015

noncomputable def g_hnwcutcodecnndv
    (x : Var) (D : Class) (R : Class) (hyp_hnwcutcodecnndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_a1i (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) hyp_hnwcutcodecnndv_1
  have p0001 :=
    @g_id (.classMem (.cv x) D)
  have p0002 :=
    @g_jca (.classMem (.cv x) D) (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0000 p0001
  have p0003 :=
    @g_westrsegndv x D R
  have p0004 :=
    @g_syl (.classMem (.cv x) D) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0002 p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0006 :=
    @g_biimpi (syn_wbr (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe)) p0005
  have p0007 :=
    @g_syl (.classMem (.cv x) D) (syn_wbr (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe)) p0004 p0006
  have p0008 :=
    @g_brex R D (syn_cwe)
  have p0009 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0008
  have p0010 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0009
  have p0011 :=
    @g_brex R D (syn_cwe)
  have p0012 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0011
  have p0013 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0012
  have p0014 :=
    @g_brex R D (syn_cwe)
  have p0015 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0014
  have p0016 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0015
  have p0017 :=
    @g_idex
  have p0018 :=
    @g_difex R (syn_cid) p0016 p0017
  have p0019 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0018
  have p0020 :=
    @g_snex (.cv x)
  have p0021 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0019 p0020
  have p0022 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0013 p0021
  have p0023 :=
    @g_brex R D (syn_cwe)
  have p0024 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0023
  have p0025 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0024
  have p0026 :=
    @g_brex R D (syn_cwe)
  have p0027 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0026
  have p0028 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0027
  have p0029 :=
    @g_idex
  have p0030 :=
    @g_difex R (syn_cid) p0028 p0029
  have p0031 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0030
  have p0032 :=
    @g_snex (.cv x)
  have p0033 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0031 p0032
  have p0034 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0025 p0033
  have p0035 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0022 p0034
  have p0036 :=
    @g_inex R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0010 p0035
  have p0037 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0038 :=
    @g_brex R D (syn_cwe)
  have p0039 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0038
  have p0040 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0039
  have p0041 :=
    @g_brex R D (syn_cwe)
  have p0042 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0041
  have p0043 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0042
  have p0044 :=
    @g_idex
  have p0045 :=
    @g_difex R (syn_cid) p0043 p0044
  have p0046 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0045
  have p0047 :=
    @g_snex (.cv x)
  have p0048 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0046 p0047
  have p0049 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0040 p0048
  have p0050 :=
    @g_elpw (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D p0049
  have p0051 :=
    @g_mpbir (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cpw D)) (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D) p0037 p0050
  have p0052 :=
    @g_pm3_2i (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cpw D)) p0036 p0051
  have p0053 :=
    @g_opelxp (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv) (syn_cpw D)
  have p0054 :=
    @g_mpbir (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cvv) (syn_cpw D))) (syn_wa (.classMem (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cpw D))) p0052 p0053
  have p0055 :=
    @g_a1i (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cvv) (syn_cpw D))) (.classMem (.cv x) D) p0054
  have p0056 :=
    @g_jca (.classMem (.cv x) D) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe)) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cvv) (syn_cpw D))) p0007 p0055
  have p0057 :=
    @g_elin (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D))
  have p0058 :=
    @g_a1i (syn_wb (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D)))) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe)) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cvv) (syn_cpw D))))) (.classMem (.cv x) D) p0057
  have p0059 :=
    @g_mpbird (.classMem (.cv x) D) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D)))) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe)) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cvv) (syn_cpw D)))) p0056 p0058
  have p0060 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes D)))
  have p0061 :=
    @g_eleq2i (syn_chwcodes D) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0060
  have p0062 :=
    @g_sylibr (.classMem (.cv x) D) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D)))) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwcodes D)) p0059 p0061
  have p0063 :=
    @g_inss2 R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0064 :=
    @g_brex R D (syn_cwe)
  have p0065 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0064
  have p0066 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0065
  have p0067 :=
    @g_brex R D (syn_cwe)
  have p0068 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0067
  have p0069 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0068
  have p0070 :=
    @g_brex R D (syn_cwe)
  have p0071 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0070
  have p0072 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0071
  have p0073 :=
    @g_idex
  have p0074 :=
    @g_difex R (syn_cid) p0072 p0073
  have p0075 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0074
  have p0076 :=
    @g_snex (.cv x)
  have p0077 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0075 p0076
  have p0078 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0069 p0077
  have p0079 :=
    @g_brex R D (syn_cwe)
  have p0080 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0079
  have p0081 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0080
  have p0082 :=
    @g_brex R D (syn_cwe)
  have p0083 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0082
  have p0084 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0083
  have p0085 :=
    @g_idex
  have p0086 :=
    @g_difex R (syn_cid) p0084 p0085
  have p0087 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0086
  have p0088 :=
    @g_snex (.cv x)
  have p0089 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0087 p0088
  have p0090 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0081 p0089
  have p0091 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0078 p0090
  have p0092 :=
    @g_inex R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0066 p0091
  have p0093 :=
    @g_brex R D (syn_cwe)
  have p0094 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0093
  have p0095 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0094
  have p0096 :=
    @g_brex R D (syn_cwe)
  have p0097 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0096
  have p0098 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0097
  have p0099 :=
    @g_idex
  have p0100 :=
    @g_difex R (syn_cid) p0098 p0099
  have p0101 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0100
  have p0102 :=
    @g_snex (.cv x)
  have p0103 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0101 p0102
  have p0104 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0095 p0103
  have p0105 :=
    @g_opfv2nd (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0092 p0104
  have p0106 :=
    @g_brex R D (syn_cwe)
  have p0107 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0106
  have p0108 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0107
  have p0109 :=
    @g_brex R D (syn_cwe)
  have p0110 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0109
  have p0111 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0110
  have p0112 :=
    @g_brex R D (syn_cwe)
  have p0113 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0112
  have p0114 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0113
  have p0115 :=
    @g_idex
  have p0116 :=
    @g_difex R (syn_cid) p0114 p0115
  have p0117 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0116
  have p0118 :=
    @g_snex (.cv x)
  have p0119 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0117 p0118
  have p0120 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0111 p0119
  have p0121 :=
    @g_brex R D (syn_cwe)
  have p0122 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0121
  have p0123 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0122
  have p0124 :=
    @g_brex R D (syn_cwe)
  have p0125 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0124
  have p0126 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0125
  have p0127 :=
    @g_idex
  have p0128 :=
    @g_difex R (syn_cid) p0126 p0127
  have p0129 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0128
  have p0130 :=
    @g_snex (.cv x)
  have p0131 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0129 p0130
  have p0132 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0123 p0131
  have p0133 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0120 p0132
  have p0134 :=
    @g_inex R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0108 p0133
  have p0135 :=
    @g_brex R D (syn_cwe)
  have p0136 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0135
  have p0137 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0136
  have p0138 :=
    @g_brex R D (syn_cwe)
  have p0139 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0138
  have p0140 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0139
  have p0141 :=
    @g_idex
  have p0142 :=
    @g_difex R (syn_cid) p0140 p0141
  have p0143 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0142
  have p0144 :=
    @g_snex (.cv x)
  have p0145 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0143 p0144
  have p0146 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0137 p0145
  have p0147 :=
    @g_opfv2nd (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0134 p0146
  have p0148 :=
    @g_pm3_2i (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0105 p0147
  have p0149 :=
    @g_xpeq12 (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0150 :=
    Nominal.mp p0148 p0149
  have p0151 :=
    @g_eqcomi (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0150
  have p0152 :=
    @g_sseq2 (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0153 :=
    Nominal.mp p0151 p0152
  have p0154 :=
    @g_mpbi (syn_wss (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wss (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0063 p0153
  have p0155 :=
    @g_brex R D (syn_cwe)
  have p0156 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0155
  have p0157 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0156
  have p0158 :=
    @g_brex R D (syn_cwe)
  have p0159 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0158
  have p0160 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0159
  have p0161 :=
    @g_brex R D (syn_cwe)
  have p0162 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0161
  have p0163 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0162
  have p0164 :=
    @g_idex
  have p0165 :=
    @g_difex R (syn_cid) p0163 p0164
  have p0166 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0165
  have p0167 :=
    @g_snex (.cv x)
  have p0168 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0166 p0167
  have p0169 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0160 p0168
  have p0170 :=
    @g_brex R D (syn_cwe)
  have p0171 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0170
  have p0172 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0171
  have p0173 :=
    @g_brex R D (syn_cwe)
  have p0174 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0173
  have p0175 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0174
  have p0176 :=
    @g_idex
  have p0177 :=
    @g_difex R (syn_cid) p0175 p0176
  have p0178 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0177
  have p0179 :=
    @g_snex (.cv x)
  have p0180 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0178 p0179
  have p0181 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0172 p0180
  have p0182 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0169 p0181
  have p0183 :=
    @g_inex R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0157 p0182
  have p0184 :=
    @g_brex R D (syn_cwe)
  have p0185 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0184
  have p0186 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0185
  have p0187 :=
    @g_brex R D (syn_cwe)
  have p0188 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0187
  have p0189 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0188
  have p0190 :=
    @g_idex
  have p0191 :=
    @g_difex R (syn_cid) p0189 p0190
  have p0192 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0191
  have p0193 :=
    @g_snex (.cv x)
  have p0194 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0192 p0193
  have p0195 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0186 p0194
  have p0196 :=
    @g_opfv1st (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0183 p0195
  have p0197 :=
    @g_sseq1 (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0198 :=
    Nominal.mp p0196 p0197
  have p0199 :=
    @g_mpbir (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) (syn_wss (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0154 p0198
  have p0200 :=
    @g_a1i (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) (.classMem (.cv x) D) p0199
  have p0201 :=
    @g_jca (.classMem (.cv x) D) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0062 p0200
  have p0202 :=
    @g_brex R D (syn_cwe)
  have p0203 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0202
  have p0204 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0203
  have p0205 :=
    @g_brex R D (syn_cwe)
  have p0206 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0205
  have p0207 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0206
  have p0208 :=
    @g_brex R D (syn_cwe)
  have p0209 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0208
  have p0210 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0209
  have p0211 :=
    @g_idex
  have p0212 :=
    @g_difex R (syn_cid) p0210 p0211
  have p0213 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0212
  have p0214 :=
    @g_snex (.cv x)
  have p0215 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0213 p0214
  have p0216 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0207 p0215
  have p0217 :=
    @g_brex R D (syn_cwe)
  have p0218 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0217
  have p0219 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0218
  have p0220 :=
    @g_brex R D (syn_cwe)
  have p0221 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0220
  have p0222 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0221
  have p0223 :=
    @g_idex
  have p0224 :=
    @g_difex R (syn_cid) p0222 p0223
  have p0225 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0224
  have p0226 :=
    @g_snex (.cv x)
  have p0227 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0225 p0226
  have p0228 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0219 p0227
  have p0229 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0216 p0228
  have p0230 :=
    @g_inex R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0204 p0229
  have p0231 :=
    @g_brex R D (syn_cwe)
  have p0232 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0231
  have p0233 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0232
  have p0234 :=
    @g_brex R D (syn_cwe)
  have p0235 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0234
  have p0236 :=
    Nominal.mp hyp_hnwcutcodecnndv_1 p0235
  have p0237 :=
    @g_idex
  have p0238 :=
    @g_difex R (syn_cid) p0236 p0237
  have p0239 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0238
  have p0240 :=
    @g_snex (.cv x)
  have p0241 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0239 p0240
  have p0242 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0233 p0241
  have p0243 :=
    @g_opex (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0230 p0242
  have p0244 :=
    @g_elhwcncl D (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0245 :=
    Nominal.mp p0243 p0244
  have p0246 :=
    @g_a1i (syn_wb (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwcn D)) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))) (.classMem (.cv x) D) p0245
  have p0247 :=
    @g_mpbird (.classMem (.cv x) D) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwcn D)) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0201 p0246
  have p0248 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x))))
  have p0249 :=
    @g_eleq1i (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwcn D) p0248
  have p0250 :=
    @g_sylibr (.classMem (.cv x) D) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) p0247 p0249
  exact p0250

noncomputable def g_hnwcutcodecnclndv
    (B : Class) (D : Class) (R : Class) (hyp_hnwcutcodecnclndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))) := by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex B D
  have p0001 :=
    @g_eleq1 (.cv x) B D
  have p0002 :=
    @g_hnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0003 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B) (syn_chwcn D) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0001 p0003
  have p0005 :=
    @g_hnwcutcodecnndv x D R hyp_hnwcutcodecnclndv_1
  have p0006 :=
    @g_vtoclg (.imp (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))) (.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))) x B (syn_cvv) dv_cache_0002 dv_cache_0003 p0004 p0005
  have p0007 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0000 p0006
  exact p0007

noncomputable def g_hnwcutrelfndv
    (D : Class) (R : Class) (hyp_hnwcutrelfndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ ((syn_cpw1 D)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_chwcn D)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_chnwcutrel R D)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutrelfn D R hyp_hnwcutrelfndv_1
  have p0001 :=
    @g_hnwpw1argcl D q
  have p0002 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0001
  have p0003 :=
    @g_hnwcutcodecnclndv (syn_cuni (.cv q)) D R hyp_hnwcutrelfndv_1
  have p0004 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D) (.classMem (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D)) p0002 p0003
  have p0005 :=
    @g_hnwcutrelval D R q hyp_hnwcutrelfndv_1
  have p0006 :=
    @g_eleq1d (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D) p0005
  have p0007 :=
    @g_mpbird (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D)) p0004 p0006
  have p0008 :=
    @g_rgen (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)) q (syn_cpw1 D) p0007
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (syn_wral q (syn_cpw1 D) (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D))) p0000 p0008
  have p0010 :=
    @g_ffnfv q (syn_cpw1 D) (syn_chwcn D) (syn_chnwcutrel R D) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0011 :=
    @g_mpbir (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) (syn_wa (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (syn_wral q (syn_cpw1 D) (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)))) p0009 p0010
  exact p0011

noncomputable def g_hnwcutsirelvalndv
    (D : Class) (R : Class) (q : Var) (hyp_hnwcutsirelvalndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q)) (syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({q} : Finset Var)
  have p0000 :=
    @g_pw12argcl (.cv q) D
  have p0001 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0000
  have p0002 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csi (syn_chnwcutrel R D)) p0001
  have p0003 :=
    @g_pw12argcl (.cv q) D
  have p0004 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0003
  have p0005 :=
    @g_snelpw1 (syn_cuni (syn_cuni (.cv q))) D
  have p0006 :=
    @g_biimpri (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0005
  have p0007 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) p0004 p0006
  have p0008 :=
    @g_hnwcutrelfndv D R hyp_hnwcutsirelvalndv_1
  have p0009 :=
    @g_sifvald (syn_cpw1 D) (syn_chwcn D) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_chnwcutrel R D) p0008
  have p0010 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) (.classEq (syn_cfv (syn_csi (syn_chnwcutrel R D)) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0007 p0009
  have p0011 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q)) (syn_cfv (syn_csi (syn_chnwcutrel R D)) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0002 p0010
  have p0012 :=
    @g_pw12argcl (.cv q) D
  have p0013 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0012
  have p0014 :=
    @g_hnwcutrelvalcld (syn_cuni (syn_cuni (.cv q))) D R hyp_hnwcutsirelvalndv_1
  have p0015 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0013 p0014
  have p0016 :=
    @g_sneqd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) p0015
  have p0017 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q)) (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0011 p0016
  exact p0017

noncomputable def g_hnwcutclassltnendv
    (x : Var) (y : Var) (D : Class) (R : Class) (hyp_hnwcutclassltnendv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_a1i (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) hyp_hnwcutclassltnendv_1
  have p0001 :=
    @g_simpl (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0002 :=
    @g_jca (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0004 :=
    @g_jca (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0002 p0003
  have p0005 :=
    @g_hnwcutcodeltnoiso x y D R
  have p0006 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))) p0004 p0005
  have p0007 :=
    @g_simpr (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0008 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))
  have p0009 :=
    @g_ssel (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) D (.cv x)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.classMem (.cv x) D) p0007 p0010
  have p0012 :=
    @g_hnwcutcodecnclndv (.cv x) D R hyp_hnwcutclassltnendv_1
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) p0011 p0012
  have p0014 :=
    @g_simpl (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0015 :=
    @g_hnwcutcodecnclndv (.cv y) D R hyp_hnwcutclassltnendv_1
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv y) D) (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)) p0014 p0015
  have p0017 :=
    @g_jca (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)) p0013 p0016
  have p0018 :=
    @g_brex R D (syn_cwe)
  have p0019 :=
    @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0020 :=
    @g_syl (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) (.classMem D (syn_cvv)) p0018 p0019
  have p0021 :=
    Nominal.mp hyp_hnwcutclassltnendv_1 p0020
  have p0022 :=
    @g_hwnisoclasseqbcl D (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D (.cv y)) p0021
  have p0023 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D))) (syn_wb (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))) p0017 p0022
  have p0024 :=
    @g_biimpd (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))) p0023
  have p0025 :=
    @g_con3d (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))) p0024
  have p0026 :=
    @g_mpd (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) p0006 p0025
  exact p0026

#print axioms g_hnwcutclassltnendv

end NFChoice.DirectNominalPrf.WPPReplay
