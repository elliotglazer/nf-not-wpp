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
import NominalWPPReplayChunk017Compact001Part092

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

noncomputable def g_cfbhnpw13genericcodepointcoverndv
    (C : Class) (Q : Class) (X : Class) (hyp_cfbhnpw13genericcodepointcoverndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_cfbhnpw13genericcodepointcoverndv_2 : Nominal.NPrf (.classMem C (syn_chwcn (syn_cpw X)))) (hyp_cfbhnpw13genericcodepointcoverndv_3 : Nominal.NPrf (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))) (hyp_cfbhnpw13genericcodepointcoverndv_4 : Nominal.NPrf (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) (hyp_cfbhnpw13genericcodepointcoverndv_5 : Nominal.NPrf (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf (.imp (syn_wwpp) (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) Q) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))))) := by
  let proofSupport : Finset Var := C.fv ∪ Q.fv ∪ X.fv
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_Q : k ∉ Q.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_not_X : k ∉ X.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : k ∉ (X).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ ((syn_cpw (syn_cpw (syn_chnord X)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : k ∉ ((Wff.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_cfbwpphwcncarrierinjndv C k X dv_cache_0001 dv_cache_0002 hyp_cfbhnpw13genericcodepointcoverndv_1 hyp_cfbhnpw13genericcodepointcoverndv_2 hyp_cfbhnpw13genericcodepointcoverndv_5
  have p0001 :=
    @g_cfbhnpw13genericraisedcodendv C X hyp_cfbhnpw13genericcodepointcoverndv_1 hyp_cfbhnpw13genericcodepointcoverndv_2
  have p0002 :=
    @g_simpr (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_f1eq2 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X))) (.cv k)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_biimpri (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X)))) p0005
  have p0007 :=
    @g_pwex X hyp_cfbhnpw13genericcodepointcoverndv_1
  have p0008 :=
    @g_pw1ex (syn_cpw X) p0007
  have p0009 :=
    @g_pw1ex (syn_cpw1 (syn_cpw X)) p0008
  have p0010 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw X))) p0009
  have p0011 :=
    @g_hnordex X hyp_cfbhnpw13genericcodepointcoverndv_1
  have p0012 :=
    @g_pwex (syn_chnord X) p0011
  have p0013 :=
    @g_pwex (syn_cpw (syn_chnord X)) p0012
  have p0014 :=
    @g_cfbhnpw13genericraisedcodendv C X hyp_cfbhnpw13genericcodepointcoverndv_1 hyp_cfbhnpw13genericcodepointcoverndv_2
  have p0015 :=
    @g_simpl (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_cfbhnqinjcodecoverdclndv (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) k (syn_cpw (syn_cpw (syn_chnord X))) dv_cache_0003 dv_cache_0004 p0010 p0013 p0016
  have p0018 :=
    @g_syl (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))))))) (syn_cpw (syn_cpw (syn_chnord X)))) (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) p0006 p0017
  have p0019 :=
    @g_exlimiv (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X)))) (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) k dv_cache_0005 p0018
  have p0020 :=
    @g_syl (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) C)))) (syn_cpw (syn_cpw (syn_chnord X))))) (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) p0000 p0019
  have p0021 :=
    @g_cfbhnpw13genericquotrepcohndv C Q X hyp_cfbhnpw13genericcodepointcoverndv_1 hyp_cfbhnpw13genericcodepointcoverndv_2 hyp_cfbhnpw13genericcodepointcoverndv_3 hyp_cfbhnpw13genericcodepointcoverndv_4
  have p0022 :=
    @g_eqcomi (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) p0021
  have p0023 :=
    @g_fveq2i (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q) (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) p0022
  have p0024 :=
    @g_eleq1i (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) p0023
  have p0025 :=
    @g_sylib (syn_wwpp) (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) p0020 p0024
  have p0026 :=
    @g_pwex X hyp_cfbhnpw13genericcodepointcoverndv_1
  have p0027 :=
    @g_hnpw13quoshiftf1ondv (syn_cpw X) p0026
  have p0028 :=
    @g_f1of (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_pm3_2i (syn_wf (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) p0029 hyp_cfbhnpw13genericcodepointcoverndv_3
  have p0031 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))) Q (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_eleq1i (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) Q) (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) p0032
  have p0034 :=
    @g_sylibr (syn_wwpp) (.classMem (syn_cfv (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q)) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) Q) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) p0025 p0033
  exact p0034

#print axioms g_cfbhnpw13genericcodepointcoverndv

end NFChoice.DirectNominalPrf.WPPReplay
