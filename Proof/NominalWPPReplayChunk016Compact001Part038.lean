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
import NominalWPPReplayChunk016Compact001Part037

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

noncomputable def g_wecomparisoncutreplttargetdfdv
    (x : Var) (D : Class) (R : Class) (S : Class) (E : Class) (dv_D_x : x ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_R_x : x ∉ R.fv) (dv_S_x : x ∉ S.fv) (hyp_wecomparisoncutreplttargetdfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  have dv_cache_0001 : x ∉ ((Wff.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, dv_S_x, dv_E_x, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, dv_S_x, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, dv_S_x, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, dv_S_x, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, dv_S_x, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, dv_S_x, dv_E_x, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, dv_E_x, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
  have p0001 :=
    @g_difeq1d (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid) p0000
  have p0002 :=
    @g_cnveqd (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) (syn_cdif R (syn_cid)) (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)) p0001
  have p0003 :=
    @g_imaeq1d (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) (syn_ccnv (syn_cdif R (syn_cid))) (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)) p0002
  have p0004 :=
    @g_ineq2d (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))) D p0003
  have p0005 :=
    @g_nceqd (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))) p0004
  have p0006 :=
    @g_eqeq2d (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))) (syn_cnc E) p0005
  have p0007 :=
    @g_rexbidv (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))))) x D dv_cache_0001 p0006
  have p0008 :=
    @g_biid (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))))))
  have p0009 :=
    @g_a1i (syn_wb (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))))))) (.classEq S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) p0008
  have p0010 :=
    @g_rexeq (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))))) x D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) dv_cache_0002 dv_cache_0003
  have p0011 :=
    @g_id (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))
  have p0012 :=
    @g_ineq1d (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))) p0011
  have p0013 :=
    @g_nceqd (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))) p0012
  have p0014 :=
    @g_eqeq2d (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))) (syn_cnc E) p0013
  have p0015 :=
    @g_rexbidv (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))))) (.classEq (syn_cnc E) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))))) x (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) dv_cache_0004 p0014
  have p0016 :=
    @g_bitrd (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (.classEq (syn_cnc E) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))))) p0010 p0015
  have p0017 :=
    @g_id (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))
  have p0018 :=
    @g_nceqd (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) p0017
  have p0019 :=
    @g_eqeq1d (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc E) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))) p0018
  have p0020 :=
    @g_rexbidv (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (.classEq (syn_cnc E) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))))) (.classEq (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x)))))) x (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) dv_cache_0005 p0019
  have p0021 :=
    @g_breq1 R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) D (syn_cwe)
  have p0022 :=
    @g_breq2 D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cwe)
  have p0023 :=
    @g_breq1 (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_csn (syn_c0c)) (syn_cwe)
  have p0024 :=
    @g_breq2 (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cwe)
  have p0025 :=
    @g_finlewe
  have p0026 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) syn_wtru p0025
  have p0027 :=
    @g_peano1
  have p0028 :=
    @g_snssi (syn_c0c) (syn_cnnc)
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_a1i (syn_wss (syn_csn (syn_c0c)) (syn_cnnc)) syn_wtru p0029
  have p0031 :=
    @g_snex (syn_c0c)
  have p0032 :=
    @g_a1i (.classMem (syn_csn (syn_c0c)) (syn_cvv)) syn_wtru p0031
  have p0033 :=
    @g_werestrndv syn_wtru (syn_csn (syn_c0c)) (syn_cnnc) (syn_ckqrel (syn_clefin)) p0026 p0030 p0032
  have p0034 :=
    @g_trud (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cwe) (syn_csn (syn_c0c))) p0033
  have p0035 :=
    @g_keephyp2v (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wbr R (syn_cwe) D) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cwe) D) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cwe) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cwe) (syn_csn (syn_c0c))) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cwe) (syn_csn (syn_c0c))) R D (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_csn (syn_c0c)) p0021 p0022 p0023 p0024 hyp_wecomparisoncutreplttargetdfdv_1 p0034
  have p0036 :=
    @g_biid (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
  have p0037 :=
    @g_a1i (syn_wb (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))) (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) p0036
  have p0038 :=
    @g_id (.classEq S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0039 :=
    @g_breq1d (.classEq S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) E (syn_cwe) p0038
  have p0040 :=
    @g_biid (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))
  have p0041 :=
    @g_a1i (syn_wb (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (.classEq S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) p0040
  have p0042 :=
    @g_anbi12d (.classEq S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) p0039 p0041
  have p0043 :=
    @g_biid (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
  have p0044 :=
    @g_a1i (syn_wb (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)) (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) p0043
  have p0045 :=
    @g_id (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))
  have p0046 :=
    @g_nceqd (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) p0045
  have p0047 :=
    @g_breq2d (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cnc D) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cnc E) (syn_cltc) p0046
  have p0048 :=
    @g_anbi12d (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0044 p0047
  have p0049 :=
    @g_id (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))
  have p0050 :=
    @g_breq2d (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) p0049
  have p0051 :=
    @g_id (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))
  have p0052 :=
    @g_nceqd (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) p0051
  have p0053 :=
    @g_breq1d (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc E) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cltc) p0052
  have p0054 :=
    @g_anbi12d (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) (syn_wbr (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0050 p0053
  have p0055 :=
    @g_biid (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))))
  have p0056 :=
    @g_a1i (syn_wb (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))))) (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) p0055
  have p0057 :=
    @g_id (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0058 :=
    @g_breq1d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_c0) (syn_cwe) p0057
  have p0059 :=
    @g_biid (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))
  have p0060 :=
    @g_a1i (syn_wb (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) p0059
  have p0061 :=
    @g_anbi12d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) p0058 p0060
  have p0062 :=
    @g_biid (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
  have p0063 :=
    @g_a1i (syn_wb (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))) (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) p0062
  have p0064 :=
    @g_id (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))
  have p0065 :=
    @g_nceqd (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) p0064
  have p0066 :=
    @g_breq2d (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cnc (syn_csn (syn_c0c))) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cnc (syn_c0)) (syn_cltc) p0065
  have p0067 :=
    @g_anbi12d (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0063 p0066
  have p0068 :=
    @g_id (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))
  have p0069 :=
    @g_breq2d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) p0068
  have p0070 :=
    @g_id (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))
  have p0071 :=
    @g_nceqd (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) p0070
  have p0072 :=
    @g_breq1d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cltc) p0071
  have p0073 :=
    @g_anbi12d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) (syn_wbr (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0069 p0072
  have p0074 :=
    @g_finlewe
  have p0075 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) syn_wtru p0074
  have p0076 :=
    @g_n_0ss (syn_cnnc)
  have p0077 :=
    @g_a1i (syn_wss (syn_c0) (syn_cnnc)) syn_wtru p0076
  have p0078 :=
    @g_n_0ex
  have p0079 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv)) syn_wtru p0078
  have p0080 :=
    @g_werestrndv syn_wtru (syn_c0) (syn_cnnc) (syn_ckqrel (syn_clefin)) p0075 p0077 p0079
  have p0081 :=
    @g_trud (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) p0080
  have p0082 :=
    @g_n_0lt1c
  have p0083 :=
    @g_df0c2
  have p0084 :=
    @g_n_0cex
  have p0085 :=
    @g_df1c3 (syn_c0c) p0084
  have p0086 :=
    @g_n_3brtr3i (syn_c0c) (syn_c1c) (syn_cnc (syn_c0)) (syn_cnc (syn_csn (syn_c0c))) (syn_cltc) p0082 p0083 p0085
  have p0087 :=
    @g_pm3_2i (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) p0081 p0086
  have p0088 :=
    @g_elimhyp4v (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))))) (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))))) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))))) R S D (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_csn (syn_c0c)) E (syn_c0) p0037 p0042 p0048 p0054 p0056 p0061 p0067 p0073 p0087
  have p0089 :=
    @g_simpli (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0088
  have p0090 :=
    @g_biid (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
  have p0091 :=
    @g_a1i (syn_wb (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))) (.classEq R (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) p0090
  have p0092 :=
    @g_id (.classEq S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0093 :=
    @g_breq1d (.classEq S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) E (syn_cwe) p0092
  have p0094 :=
    @g_biid (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))
  have p0095 :=
    @g_a1i (syn_wb (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (.classEq S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) p0094
  have p0096 :=
    @g_anbi12d (.classEq S (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) p0093 p0095
  have p0097 :=
    @g_biid (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
  have p0098 :=
    @g_a1i (syn_wb (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)) (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) p0097
  have p0099 :=
    @g_id (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))
  have p0100 :=
    @g_nceqd (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) p0099
  have p0101 :=
    @g_breq2d (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cnc D) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cnc E) (syn_cltc) p0100
  have p0102 :=
    @g_anbi12d (.classEq D (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0098 p0101
  have p0103 :=
    @g_id (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))
  have p0104 :=
    @g_breq2d (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) p0103
  have p0105 :=
    @g_id (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))
  have p0106 :=
    @g_nceqd (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) p0105
  have p0107 :=
    @g_breq1d (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc E) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cltc) p0106
  have p0108 :=
    @g_anbi12d (.classEq E (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) (syn_wbr (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0104 p0107
  have p0109 :=
    @g_biid (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))))
  have p0110 :=
    @g_a1i (syn_wb (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))))) (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))) p0109
  have p0111 :=
    @g_id (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0112 :=
    @g_breq1d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_c0) (syn_cwe) p0111
  have p0113 :=
    @g_biid (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))
  have p0114 :=
    @g_a1i (syn_wb (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) p0113
  have p0115 :=
    @g_anbi12d (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) p0112 p0114
  have p0116 :=
    @g_biid (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
  have p0117 :=
    @g_a1i (syn_wb (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))) (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) p0116
  have p0118 :=
    @g_id (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))
  have p0119 :=
    @g_nceqd (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) p0118
  have p0120 :=
    @g_breq2d (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cnc (syn_csn (syn_c0c))) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cnc (syn_c0)) (syn_cltc) p0119
  have p0121 :=
    @g_anbi12d (.classEq (syn_csn (syn_c0c)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0117 p0120
  have p0122 :=
    @g_id (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))
  have p0123 :=
    @g_breq2d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) p0122
  have p0124 :=
    @g_id (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)))
  have p0125 :=
    @g_nceqd (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) p0124
  have p0126 :=
    @g_breq1d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_c0)) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))) (syn_cltc) p0125
  have p0127 :=
    @g_anbi12d (.classEq (syn_c0) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) (syn_wbr (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0123 p0126
  have p0128 :=
    @g_finlewe
  have p0129 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) syn_wtru p0128
  have p0130 :=
    @g_n_0ss (syn_cnnc)
  have p0131 :=
    @g_a1i (syn_wss (syn_c0) (syn_cnnc)) syn_wtru p0130
  have p0132 :=
    @g_n_0ex
  have p0133 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv)) syn_wtru p0132
  have p0134 :=
    @g_werestrndv syn_wtru (syn_c0) (syn_cnnc) (syn_ckqrel (syn_clefin)) p0129 p0131 p0133
  have p0135 :=
    @g_trud (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) p0134
  have p0136 :=
    @g_n_0lt1c
  have p0137 :=
    @g_df0c2
  have p0138 :=
    @g_n_0cex
  have p0139 :=
    @g_df1c3 (syn_c0c) p0138
  have p0140 :=
    @g_n_3brtr3i (syn_c0c) (syn_c1c) (syn_cnc (syn_c0)) (syn_cnc (syn_csn (syn_c0c))) (syn_cltc) p0136 p0137 p0139
  have p0141 :=
    @g_pm3_2i (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) p0135 p0140
  have p0142 :=
    @g_elimhyp4v (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))))) (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))))) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c)))))) R S D (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_csn (syn_c0c)) E (syn_c0) p0091 p0096 p0102 p0108 p0110 p0115 p0121 p0127 p0141
  have p0143 :=
    @g_simpri (syn_wbr (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_wbr (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))) p0142
  have p0144 :=
    @g_wecomparisoncutrepltfdv x (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0)) dv_cache_0003 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0035 p0089 p0143
  have p0145 :=
    @g_dedth4v (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (.classEq (syn_cnc E) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (.classEq (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid))) (syn_csn (.cv x))))))) R S D E (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_csn (syn_c0c)) (syn_c0) p0007 p0009 p0016 p0020 p0144
  exact p0145

#print axioms g_wecomparisoncutreplttargetdfdv

end NFChoice.DirectNominalPrf.WPPReplay
