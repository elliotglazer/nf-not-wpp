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
import NominalWPPReplayChunk015Compact001Part023

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

noncomputable def g_nntctcnn
    (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem (syn_ctc N) (syn_ctcnn))) := by
  let proofSupport : Finset Var := N.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (h)
  have dv_cache_0001 : q ∉ ((syn_csn N)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_cnnc))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_ctc N))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_ctc N)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_snelpw1 N (syn_cnnc)
  have p0001 :=
    @g_biimpri (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) (.classMem N (syn_cnnc)) p0000
  have p0002 :=
    @g_snelpw1 N (syn_cnnc)
  have p0003 :=
    @g_biimpri (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) (.classMem N (syn_cnnc)) p0002
  have p0004 :=
    @g_fvres (syn_csn N) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0005 :=
    @g_syl (.classMem N (syn_cnnc)) (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_cfv (syn_ctcfn) (syn_csn N))) p0003 p0004
  have p0006 :=
    @g_id (.classMem N (syn_cnnc))
  have p0007 :=
    @g_elex N (syn_cnnc)
  have p0008 :=
    @g_syl (.classMem N (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem N (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_tcfnfvcl N
  have p0010 :=
    @g_syl (.classMem N (syn_cnnc)) (.classMem N (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn N)) (syn_ctc N)) p0008 p0009
  have p0011 :=
    @g_eqtrd (.classMem N (syn_cnnc)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_cfv (syn_ctcfn) (syn_csn N)) (syn_ctc N) p0005 p0010
  have p0012 :=
    @g_jca (.classMem N (syn_cnnc)) (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_ctc N)) p0001 p0011
  have p0013 :=
    @g_id (.classEq (.cv q) (syn_csn N))
  have p0014 :=
    @g_fveq2d (.classEq (.cv q) (syn_csn N)) (.cv q) (syn_csn N) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) p0013
  have p0015 :=
    @g_eqeq1d (.classEq (.cv q) (syn_csn N)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_ctc N) p0014
  have p0016 :=
    @g_rspcev (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc N)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_ctc N)) q (syn_csn N) (syn_cpw1 (syn_cnnc)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0015
  have p0017 :=
    @g_syl (.classMem N (syn_cnnc)) (syn_wa (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_ctc N))) (syn_wrex q (syn_cpw1 (syn_cnnc)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc N))) p0012 p0016
  have p0018 :=
    @g_eltcnn (syn_ctc N) q dv_cache_0004
  have p0019 :=
    @g_biimpri (.classMem (syn_ctc N) (syn_ctcnn)) (syn_wrex q (syn_cpw1 (syn_cnnc)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc N))) p0018
  have p0020 :=
    @g_syl (.classMem N (syn_cnnc)) (syn_wrex q (syn_cpw1 (syn_cnnc)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc N))) (.classMem (syn_ctc N) (syn_ctcnn)) p0017 p0019
  exact p0020

noncomputable def g_tcnnsuc
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_ctcnn)) (.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn))) := by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((Wff.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eltcnn A q dv_cache_0001
  have p0001 :=
    @g_biimpi (.classMem A (syn_ctcnn)) (syn_wrex q (syn_cpw1 (syn_cnnc)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) p0000
  have p0002 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)
  have p0003 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0004 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0005 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0003 p0004
  have p0006 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0002 p0005
  have p0007 :=
    @g_peano2 (syn_cuni (.cv q))
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classMem (syn_cplc (syn_cuni (.cv q)) (syn_c1c)) (syn_cnnc)) p0006 p0007
  have p0009 :=
    @g_nntctcnn (syn_cplc (syn_cuni (.cv q)) (syn_c1c))
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (syn_cplc (syn_cuni (.cv q)) (syn_c1c)) (syn_cnnc)) (.classMem (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c))) (syn_ctcnn)) p0008 p0009
  have p0011 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)
  have p0012 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0013 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0014 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0012 p0013
  have p0015 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0011 p0014
  have p0016 :=
    @g_nntcsuc (syn_cuni (.cv q))
  have p0017 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c))) (syn_cplc (syn_ctc (syn_cuni (.cv q))) (syn_c1c))) p0015 p0016
  have p0018 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)
  have p0019 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0020 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q))) p0018 p0019
  have p0021 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)
  have p0022 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0023 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0024 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0022 p0023
  have p0025 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0024
  have p0026 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q))))) p0021 p0025
  have p0027 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) p0020 p0026
  have p0028 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)
  have p0029 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0030 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0031 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0029 p0030
  have p0032 :=
    @g_elex (syn_cuni (.cv q)) (syn_cnnc)
  have p0033 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0031 p0032
  have p0034 :=
    @g_tcfnfvcl (syn_cuni (.cv q))
  have p0035 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))) p0033 p0034
  have p0036 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))) p0028 p0035
  have p0037 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))) p0027 p0036
  have p0038 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)
  have p0039 :=
    @g_eqtr3d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc (syn_cuni (.cv q))) A p0037 p0038
  have p0040 :=
    @g_addceq1d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (syn_ctc (syn_cuni (.cv q))) A (syn_c1c) p0039
  have p0041 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c))) (syn_cplc (syn_ctc (syn_cuni (.cv q))) (syn_c1c)) (syn_cplc A (syn_c1c)) p0017 p0040
  have p0042 :=
    @g_eleq1d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c))) (syn_cplc A (syn_c1c)) (syn_ctcnn) p0041
  have p0043 :=
    @g_mpbid (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c))) (syn_ctcnn)) (.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn)) p0010 p0042
  have p0044 :=
    @g_rexlimiva (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A) (.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn)) q (syn_cpw1 (syn_cnnc)) dv_cache_0002 p0043
  have p0045 :=
    @g_syl (.classMem A (syn_ctcnn)) (syn_wrex q (syn_cpw1 (syn_cnnc)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) (.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn)) p0001 p0044
  exact p0045

noncomputable def g_nntcnn
    (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem N (syn_ctcnn))) := by
  let proofSupport : Finset Var := N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_ctcnn)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (.cv y) (syn_ctcnn))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classMem (.cv x) (syn_ctcnn))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_c0c) (syn_ctcnn))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classMem N (syn_ctcnn))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_ctcnn))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_tcnnex
  have p0001 :=
    @g_abid2 x (syn_ctcnn) dv_cache_0001
  have p0002 :=
    @g_eleq1i (.cab x (.classMem (.cv x) (syn_ctcnn))) (syn_ctcnn) (syn_cvv) p0001
  have p0003 :=
    @g_mpbir (.classMem (.cab x (.classMem (.cv x) (syn_ctcnn))) (syn_cvv)) (.classMem (syn_ctcnn) (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_id (.classEq (.cv x) (syn_c0c))
  have p0005 :=
    @g_eleq1d (.classEq (.cv x) (syn_c0c)) (.cv x) (syn_c0c) (syn_ctcnn) p0004
  have p0006 :=
    @g_id (.classEq (.cv x) (.cv y))
  have p0007 :=
    @g_eleq1d (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) (syn_ctcnn) p0006
  have p0008 :=
    @g_id (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
  have p0009 :=
    @g_eleq1d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.cv x) (syn_cplc (.cv y) (syn_c1c)) (syn_ctcnn) p0008
  have p0010 :=
    @g_id (.classEq (.cv x) N)
  have p0011 :=
    @g_eleq1d (.classEq (.cv x) N) (.cv x) N (syn_ctcnn) p0010
  have p0012 :=
    @g_peano1
  have p0013 :=
    @g_nntctcnn (syn_c0c)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_tc0c
  have p0016 :=
    @g_eleq1i (syn_ctc (syn_c0c)) (syn_c0c) (syn_ctcnn) p0015
  have p0017 :=
    @g_mpbi (.classMem (syn_ctc (syn_c0c)) (syn_ctcnn)) (.classMem (syn_c0c) (syn_ctcnn)) p0014 p0016
  have p0018 :=
    @g_tcnnsuc (.cv y)
  have p0019 :=
    @g_a1i (.imp (.classMem (.cv y) (syn_ctcnn)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_ctcnn))) (.classMem (.cv y) (syn_cnnc)) p0018
  have p0020_e02_recanon : Nominal.NPrf (.imp (.objEq x y) (syn_wb (.classMem (.cv x) (syn_ctcnn)) (.classMem (.cv y) (syn_ctcnn)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctcnn syn_crn syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_cvv syn_cres syn_cin syn_cxp syn_copab syn_ctcfn syn_cmpt syn_c1c syn_ctc syn_cio syn_cuni syn_csn syn_cpw1 syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0020 :=
    @g_finds (.classMem (.cv x) (syn_ctcnn)) (.classMem (syn_c0c) (syn_ctcnn)) (.classMem (.cv y) (syn_ctcnn)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_ctcnn)) (.classMem N (syn_ctcnn)) x y N dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0003 p0005 p0020_e02_recanon p0009 p0011 p0017 p0019
  exact p0020

noncomputable def g_tcnnfo
     :
    Nominal.NPrf (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : q ∉ ((syn_cnnc)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_ctcnn)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_tcnnresfn
  have p0001 :=
    (by simpa [syn_ctcnn] using (Nominal.classEqRefl (syn_ctcnn)))
  have p0002 :=
    @g_eqcomi (syn_ctcnn) (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) p0001
  have p0003 :=
    @g_tcnnssnn
  have p0004 :=
    @g_nntcnn (.cv q)
  have p0005 :=
    @g_ssriv q (syn_cnnc) (syn_ctcnn) dv_cache_0001 dv_cache_0002 p0004
  have p0006 :=
    @g_eqssi (syn_ctcnn) (syn_cnnc) p0003 p0005
  have p0007 :=
    @g_eqtri (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_ctcnn) (syn_cnnc) p0002 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc))) (.classEq (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_cnnc)) p0000 p0007
  have p0009 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))))
  have p0010 :=
    @g_mpbir (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (syn_wa (syn_wfn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc))) (.classEq (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_cnnc))) p0008 p0009
  exact p0010

#print axioms g_tcnnfo

end NFChoice.DirectNominalPrf.WPPReplay
