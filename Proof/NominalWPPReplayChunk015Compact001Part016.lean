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
import NominalWPPReplayChunk015Compact001Part015

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

noncomputable def g_frecdomfv
    (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cdm F))) := by
  let proofSupport : Finset Var := F.fv ∪ I.fv ∪ N.fv
  have p0000 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0001 :=
    @g_eqid (syn_cfrec F I)
  have p0002 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0004 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0005 :=
    @g_fnfrec (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0001 p0002 p0003 p0004
  have p0006 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0007 :=
    @g_elex F (syn_cfuns)
  have p0008 :=
    @g_syl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem F (syn_cfuns)) (.classMem F (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_eqid (syn_cfrec F I)
  have p0010 :=
    @g_frecxpg (syn_cfrec F I) F I (syn_cvv) p0009
  have p0011 :=
    @g_syl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem F (syn_cvv)) (syn_wss (syn_cfrec F I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I)))) p0008 p0010
  have p0012 :=
    @g_rnss (syn_cfrec F I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I)))
  have p0013 :=
    @g_syl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wss (syn_cfrec F I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I)))) (syn_wss (syn_crn (syn_cfrec F I)) (syn_crn (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I))))) p0011 p0012
  have p0014 :=
    @g_rnxpss (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I))
  have p0015 :=
    @g_syl6ss (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_crn (syn_cfrec F I)) (syn_crn (syn_cxp (syn_cnnc) (syn_cun (syn_crn F) (syn_csn I)))) (syn_cun (syn_crn F) (syn_csn I)) p0013 p0014
  have p0016 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0017 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0018 :=
    @g_snssd (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) I (syn_cdm F) p0017
  have p0019 :=
    @g_unssd (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_crn F) (syn_csn I) (syn_cdm F) p0016 p0018
  have p0020 :=
    @g_sstrd (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_crn (syn_cfrec F I)) (syn_cun (syn_crn F) (syn_csn I)) (syn_cdm F) p0015 p0019
  have p0021 :=
    @g_jca (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wfn (syn_cfrec F I) (syn_cnnc)) (syn_wss (syn_crn (syn_cfrec F I)) (syn_cdm F)) p0005 p0020
  have p0022 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F))))
  have p0023 :=
    @g_biimpri (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)) (syn_wa (syn_wfn (syn_cfrec F I) (syn_cnnc)) (syn_wss (syn_crn (syn_cfrec F I)) (syn_cdm F))) p0022
  have p0024 :=
    @g_syl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wa (syn_wfn (syn_cfrec F I) (syn_cnnc)) (syn_wss (syn_crn (syn_cfrec F I)) (syn_cdm F))) (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)) p0021 p0023
  have p0025 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)) p0000 p0024
  have p0026 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0027 :=
    @g_jca (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)) (.classMem N (syn_cnnc)) p0025 p0026
  have p0028 :=
    @g_ffvelrn (syn_cnnc) (syn_cdm F) N (syn_cfrec F I)
  have p0029 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa (syn_wf (syn_cfrec F I) (syn_cnnc) (syn_cdm F)) (.classMem N (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cdm F)) p0027 p0028
  exact p0029

noncomputable def g_funeqfix
    (A : Class) (P : Class) (Q : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wb (.classMem A (syn_cfix (syn_ccom (syn_ccnv P) Q))) (.classEq (syn_cfv P A) (syn_cfv Q A)))) := by
  let proofSupport : Finset Var := A.fv ∪ P.fv ∪ Q.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_P : z ∉ P.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_Q : z ∉ Q.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_ccnv P)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (Q).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_P, fresh_z_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cfv Q A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cfv P A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elfix A (syn_ccom (syn_ccnv P) Q)
  have p0001 :=
    @g_brco z A A (syn_ccnv P) Q dv_cache_0001 dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_bitri (.classMem A (syn_cfix (syn_ccom (syn_ccnv P) Q))) (syn_wbr A (syn_ccom (syn_ccnv P) Q) A) (syn_wex z (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A))) p0000 p0001
  have p0003 :=
    @g_a1i (syn_wb (.classMem A (syn_cfix (syn_ccom (syn_ccnv P) Q))) (syn_wex z (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A)))) (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) p0002
  have p0004 :=
    @g_simp2 (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))
  have p0005 :=
    @g_simp3 (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))
  have p0006 :=
    @g_simpr (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))
  have p0007 :=
    @g_syl (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))) (.classMem A (syn_cdm Q)) p0005 p0006
  have p0008 :=
    @g_jca (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wfun Q) (.classMem A (syn_cdm Q)) p0004 p0007
  have p0009 :=
    @g_funbrfvb A (.cv z) Q
  have p0010 :=
    @g_syl (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wa (syn_wfun Q) (.classMem A (syn_cdm Q))) (syn_wb (.classEq (syn_cfv Q A) (.cv z)) (syn_wbr A Q (.cv z))) p0008 p0009
  have p0011 :=
    @g_bicomd (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (.classEq (syn_cfv Q A) (.cv z)) (syn_wbr A Q (.cv z)) p0010
  have p0012 :=
    @g_brcnv (.cv z) A P
  have p0013 :=
    @g_a1i (syn_wb (syn_wbr (.cv z) (syn_ccnv P) A) (syn_wbr A P (.cv z))) (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) p0012
  have p0014 :=
    @g_simp1 (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))
  have p0015 :=
    @g_simp3 (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))
  have p0016 :=
    @g_simpl (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))
  have p0017 :=
    @g_syl (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q))) (.classMem A (syn_cdm P)) p0015 p0016
  have p0018 :=
    @g_jca (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wfun P) (.classMem A (syn_cdm P)) p0014 p0017
  have p0019 :=
    @g_funbrfvb A (.cv z) P
  have p0020 :=
    @g_syl (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wa (syn_wfun P) (.classMem A (syn_cdm P))) (syn_wb (.classEq (syn_cfv P A) (.cv z)) (syn_wbr A P (.cv z))) p0018 p0019
  have p0021 :=
    @g_bicomd (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (.classEq (syn_cfv P A) (.cv z)) (syn_wbr A P (.cv z)) p0020
  have p0022 :=
    @g_bitrd (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wbr (.cv z) (syn_ccnv P) A) (syn_wbr A P (.cv z)) (.classEq (syn_cfv P A) (.cv z)) p0013 p0021
  have p0023 :=
    @g_anbi12d (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wbr A Q (.cv z)) (.classEq (syn_cfv Q A) (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A) (.classEq (syn_cfv P A) (.cv z)) p0011 p0022
  have p0024 :=
    @g_exbidv (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A)) (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z))) z dv_cache_0004 p0023
  have p0025 :=
    @g_eqcom (syn_cfv Q A) (.cv z)
  have p0026 :=
    @g_eqcom (syn_cfv P A) (.cv z)
  have p0027 :=
    @g_anbi12i (.classEq (syn_cfv Q A) (.cv z)) (.classEq (.cv z) (syn_cfv Q A)) (.classEq (syn_cfv P A) (.cv z)) (.classEq (.cv z) (syn_cfv P A)) p0025 p0026
  have p0028 :=
    @g_exbii (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z))) (syn_wa (.classEq (.cv z) (syn_cfv Q A)) (.classEq (.cv z) (syn_cfv P A))) z p0027
  have p0029 :=
    @g_fvex A Q
  have p0030 :=
    @g_eqvinc z (syn_cfv Q A) (syn_cfv P A) dv_cache_0005 dv_cache_0006 p0029
  have p0031 :=
    @g_bicomi (.classEq (syn_cfv Q A) (syn_cfv P A)) (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv Q A)) (.classEq (.cv z) (syn_cfv P A)))) p0030
  have p0032 :=
    @g_bitri (syn_wex z (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z)))) (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv Q A)) (.classEq (.cv z) (syn_cfv P A)))) (.classEq (syn_cfv Q A) (syn_cfv P A)) p0028 p0031
  have p0033 :=
    @g_eqcom (syn_cfv Q A) (syn_cfv P A)
  have p0034 :=
    @g_bitri (syn_wex z (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z)))) (.classEq (syn_cfv Q A) (syn_cfv P A)) (.classEq (syn_cfv P A) (syn_cfv Q A)) p0032 p0033
  have p0035 :=
    @g_a1i (syn_wb (syn_wex z (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z)))) (.classEq (syn_cfv P A) (syn_cfv Q A))) (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) p0034
  have p0036 :=
    @g_bitrd (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (syn_wex z (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A))) (syn_wex z (syn_wa (.classEq (syn_cfv Q A) (.cv z)) (.classEq (syn_cfv P A) (.cv z)))) (.classEq (syn_cfv P A) (syn_cfv Q A)) p0024 p0035
  have p0037 :=
    @g_bitrd (syn_w3a (syn_wfun P) (syn_wfun Q) (syn_wa (.classMem A (syn_cdm P)) (.classMem A (syn_cdm Q)))) (.classMem A (syn_cfix (syn_ccom (syn_ccnv P) Q))) (syn_wex z (syn_wa (syn_wbr A Q (.cv z)) (syn_wbr (.cv z) (syn_ccnv P) A))) (.classEq (syn_cfv P A) (syn_cfv Q A)) p0003 p0036
  exact p0037

noncomputable def g_frecteqex
    (F : Class) (G : Class) (I : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem (syn_cfrecteq F G I) (syn_cvv))) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ I.fv
  have p0000 :=
    @g_tcfnex
  have p0001 :=
    @g_a1i (.classMem (syn_ctcfn) (syn_cvv)) (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) p0000
  have p0002 :=
    @g_simpl (.classMem F (syn_cvv)) (.classMem G (syn_cvv))
  have p0003 :=
    @g_eqid (syn_cfrec F I)
  have p0004 :=
    @g_frecexg (syn_cfrec F I) F I (syn_cvv) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem F (syn_cvv)) (.classMem (syn_cfrec F I) (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_siexg (syn_cfrec F I) (syn_cvv)
  have p0007 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem (syn_cfrec F I) (syn_cvv)) (.classMem (syn_csi (syn_cfrec F I)) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_jca (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem (syn_ctcfn) (syn_cvv)) (.classMem (syn_csi (syn_cfrec F I)) (syn_cvv)) p0001 p0007
  have p0009 :=
    @g_coexg (syn_ctcfn) (syn_csi (syn_cfrec F I)) (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (.classMem (syn_ctcfn) (syn_cvv)) (.classMem (syn_csi (syn_cfrec F I)) (syn_cvv))) (.classMem (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_cnvexg (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_cvv)
  have p0012 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_cvv)) (.classMem (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_simpr (.classMem F (syn_cvv)) (.classMem G (syn_cvv))
  have p0014 :=
    @g_eqid (syn_cfrec G (syn_ctc I))
  have p0015 :=
    @g_frecexg (syn_cfrec G (syn_ctc I)) G (syn_ctc I) (syn_cvv) p0014
  have p0016 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem G (syn_cvv)) (.classMem (syn_cfrec G (syn_ctc I)) (syn_cvv)) p0013 p0015
  have p0017 :=
    @g_tcfnex
  have p0018 :=
    @g_a1i (.classMem (syn_ctcfn) (syn_cvv)) (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) p0017
  have p0019 :=
    @g_jca (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem (syn_cfrec G (syn_ctc I)) (syn_cvv)) (.classMem (syn_ctcfn) (syn_cvv)) p0016 p0018
  have p0020 :=
    @g_coexg (syn_cfrec G (syn_ctc I)) (syn_ctcfn) (syn_cvv) (syn_cvv)
  have p0021 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (.classMem (syn_cfrec G (syn_ctc I)) (syn_cvv)) (.classMem (syn_ctcfn) (syn_cvv))) (.classMem (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_jca (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_cvv)) (.classMem (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_cvv)) p0012 p0021
  have p0023 :=
    @g_coexg (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (.classMem (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_cvv)) (.classMem (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_cvv))) (.classMem (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))) (syn_cvv)) p0022 p0023
  have p0025 :=
    @g_fixexg (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))) (syn_cvv)
  have p0026 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))) (syn_cvv)) (.classMem (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))) (syn_cvv)) p0024 p0025
  have p0027 :=
    @g_uni1exg (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))) (syn_cvv)
  have p0028 :=
    @g_syl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))) (syn_cvv)) (.classMem (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) (syn_cvv)) p0026 p0027
  have p0029 :=
    (by simpa [syn_cfrecteq] using (Nominal.classEqRefl (syn_cfrecteq F G I)))
  have p0030 :=
    @g_eleq1i (syn_cfrecteq F G I) (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) (syn_cvv) p0029
  have p0031 :=
    @g_sylibr (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) (syn_cvv)) (.classMem (syn_cfrecteq F G I) (syn_cvv)) p0028 p0030
  exact p0031

noncomputable def g_sifnvalv
    (x : Var) (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv x))) (syn_csn (syn_cfv F (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ F.fv
  have p0000 :=
    @g_eqid (syn_cfv F (.cv x))
  have p0001 :=
    @g_a1i (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x))) (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) p0000
  have p0002 :=
    @g_fnopfvb A (.cv x) (syn_cfv F (.cv x)) F
  have p0003 :=
    @g_mpbid (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x))) (.classMem (syn_cop (.cv x) (syn_cfv F (.cv x))) F) p0001 p0002
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_fvex (.cv x) F
  have p0006 :=
    @g_opsnelsi (.cv x) (syn_cfv F (.cv x)) F p0004 p0005
  have p0007 :=
    @g_sylibr (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) (syn_cfv F (.cv x))) F) (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (syn_cfv F (.cv x)))) (syn_csi F)) p0003 p0006
  have p0008 :=
    @g_simpl (syn_wfn F A) (.classMem (.cv x) A)
  have p0009 :=
    @g_fnfun A F
  have p0010 :=
    @g_syl (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (syn_wfn F A) (syn_wfun F) p0008 p0009
  have p0011 :=
    @g_funsi F
  have p0012 :=
    @g_syl (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (syn_wfun F) (syn_wfun (syn_csi F)) p0010 p0011
  have p0013 :=
    @g_funopfv (syn_csn (.cv x)) (syn_csn (syn_cfv F (.cv x))) (syn_csi F)
  have p0014 :=
    @g_syl (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (syn_wfun (syn_csi F)) (.imp (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (syn_cfv F (.cv x)))) (syn_csi F)) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv x))) (syn_csn (syn_cfv F (.cv x))))) p0012 p0013
  have p0015 :=
    @g_mpd (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (syn_cfv F (.cv x)))) (syn_csi F)) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv x))) (syn_csn (syn_cfv F (.cv x)))) p0007 p0014
  exact p0015

noncomputable def g_tcfnfv
    (A : Class) (hyp_tcfnfv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_ctcfn) (syn_csn A)) (syn_ctc A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_eqid (syn_ctc A)
  have p0001 :=
    @g_brtcfn A (syn_ctc A) hyp_tcfnfv_1
  have p0002 :=
    @g_mpbir (syn_wbr (syn_csn A) (syn_ctcfn) (syn_ctc A)) (.classEq (syn_ctc A) (syn_ctc A)) p0000 p0001
  have p0003 :=
    @g_fntcfn
  have p0004 :=
    @g_snel1c A hyp_tcfnfv_1
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn A) (syn_c1c)) p0003 p0004
  have p0006 :=
    @g_fnbrfvb (syn_c1c) (syn_csn A) (syn_ctc A) (syn_ctcfn)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_mpbir (.classEq (syn_cfv (syn_ctcfn) (syn_csn A)) (syn_ctc A)) (syn_wbr (syn_csn A) (syn_ctcfn) (syn_ctc A)) p0002 p0007
  exact p0008

noncomputable def g_frecteqval
    (n : Var) (F : Class) (G : Class) (I : Class) (hyp_frecteqval_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_frecteqval_2 : Nominal.NPrf (.classMem I (syn_cdm F))) (hyp_frecteqval_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_frecteqval_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_frecteqval_5 : Nominal.NPrf (.classMem (syn_ctc I) (syn_cdm G))) (hyp_frecteqval_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n)))))) := by
  let proofSupport : Finset Var := ({n} : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv
  have p0000 :=
    (by simpa [syn_cfrecteq] using (Nominal.classEqRefl (syn_cfrecteq F G I)))
  have p0001 :=
    @g_eleq2i (syn_cfrecteq F G I) (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) (.cv n) p0000
  have p0002 :=
    @g_vex n
  have p0003 :=
    @g_eluni1 (.cv n) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))) p0002
  have p0004 :=
    @g_bitri (.classMem (.cv n) (syn_cfrecteq F G I)) (.classMem (.cv n) (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))))) (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) p0001 p0003
  have p0005 :=
    @g_a1i (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I)) (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))))) (.classMem (.cv n) (syn_cnnc)) p0004
  have p0006 :=
    @g_fntcfn
  have p0007 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_frecteqval_1 hyp_frecteqval_2 hyp_frecteqval_3
  have p0010 :=
    @g_eqid (syn_cfrec F I)
  have p0011 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0012 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0013 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0014 :=
    @g_fnfrec (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0010 p0011 p0012 p0013
  have p0015 :=
    Nominal.mp p0009 p0014
  have p0016 :=
    @g_fnfun (syn_cnnc) (syn_cfrec F I)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_funsi (syn_cfrec F I)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (syn_wfun (syn_csi (syn_cfrec F I))) p0008 p0019
  have p0021 :=
    @g_funco (syn_ctcfn) (syn_csi (syn_cfrec F I))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_a1i (syn_wfun (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (.classMem (.cv n) (syn_cnnc)) p0022
  have p0024 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_frecteqval_4 hyp_frecteqval_5 hyp_frecteqval_6
  have p0025 :=
    @g_eqid (syn_cfrec G (syn_ctc I))
  have p0026 :=
    @g_simp1 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))
  have p0027 :=
    @g_simp2 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))
  have p0028 :=
    @g_simp3 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))
  have p0029 :=
    @g_fnfrec (syn_w3a (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))) (syn_cfrec G (syn_ctc I)) G (syn_ctc I) p0025 p0026 p0027 p0028
  have p0030 :=
    Nominal.mp p0024 p0029
  have p0031 :=
    @g_fnfun (syn_cnnc) (syn_cfrec G (syn_ctc I))
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_fntcfn
  have p0034 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0035 :=
    Nominal.mp p0033 p0034
  have p0036 :=
    @g_pm3_2i (syn_wfun (syn_cfrec G (syn_ctc I))) (syn_wfun (syn_ctcfn)) p0032 p0035
  have p0037 :=
    @g_funco (syn_cfrec G (syn_ctc I)) (syn_ctcfn)
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_a1i (syn_wfun (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))) (.classMem (.cv n) (syn_cnnc)) p0038
  have p0040 :=
    @g_fvex (.cv n) (syn_cfrec F I)
  have p0041 :=
    @g_snel1c (syn_cfv (syn_cfrec F I) (.cv n)) p0040
  have p0042 :=
    @g_fntcfn
  have p0043 :=
    @g_fndm (syn_c1c) (syn_ctcfn)
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_eleq2i (syn_cdm (syn_ctcfn)) (syn_c1c) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) p0044
  have p0046 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cdm (syn_ctcfn))) (.classMem (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_c1c)) p0041 p0045
  have p0047 :=
    @g_a1i (.classMem (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cdm (syn_ctcfn))) (.classMem (.cv n) (syn_cnnc)) p0046
  have p0048 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_frecteqval_1 hyp_frecteqval_2 hyp_frecteqval_3
  have p0049 :=
    @g_eqid (syn_cfrec F I)
  have p0050 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0051 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0052 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0053 :=
    @g_fnfrec (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0049 p0050 p0051 p0052
  have p0054 :=
    Nominal.mp p0048 p0053
  have p0055 :=
    @g_sifnvalv n (syn_cnnc) (syn_cfrec F I)
  have p0056 :=
    @g_mpan (syn_wfn (syn_cfrec F I) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n)))) p0054 p0055
  have p0057 :=
    @g_eleq1d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cdm (syn_ctcfn)) p0056
  have p0058 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_cdm (syn_ctcfn))) (.classMem (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cdm (syn_ctcfn))) p0047 p0057
  have p0059 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_frecteqval_1 hyp_frecteqval_2 hyp_frecteqval_3
  have p0060 :=
    @g_eqid (syn_cfrec F I)
  have p0061 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0062 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0063 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0064 :=
    @g_fnfrec (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0060 p0061 p0062 p0063
  have p0065 :=
    Nominal.mp p0059 p0064
  have p0066 :=
    @g_fnfun (syn_cnnc) (syn_cfrec F I)
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_funsi (syn_cfrec F I)
  have p0069 :=
    Nominal.mp p0067 p0068
  have p0070 :=
    @g_a1i (syn_wfun (syn_csi (syn_cfrec F I))) (.classMem (.cv n) (syn_cnnc)) p0069
  have p0071 :=
    @g_snelpw1 (.cv n) (syn_cnnc)
  have p0072 :=
    @g_biimpri (.classMem (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0071
  have p0073 :=
    @g_dmsi (syn_cfrec F I)
  have p0074 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_frecteqval_1 hyp_frecteqval_2 hyp_frecteqval_3
  have p0075 :=
    @g_eqid (syn_cfrec F I)
  have p0076 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0077 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0078 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0079 :=
    @g_fnfrec (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0075 p0076 p0077 p0078
  have p0080 :=
    Nominal.mp p0074 p0079
  have p0081 :=
    @g_fndm (syn_cnnc) (syn_cfrec F I)
  have p0082 :=
    Nominal.mp p0080 p0081
  have p0083 :=
    @g_pw1eq (syn_cdm (syn_cfrec F I)) (syn_cnnc)
  have p0084 :=
    Nominal.mp p0082 p0083
  have p0085 :=
    @g_eqtri (syn_cdm (syn_csi (syn_cfrec F I))) (syn_cpw1 (syn_cdm (syn_cfrec F I))) (syn_cpw1 (syn_cnnc)) p0073 p0084
  have p0086 :=
    @g_eleq2i (syn_cdm (syn_csi (syn_cfrec F I))) (syn_cpw1 (syn_cnnc)) (syn_csn (.cv n)) p0085
  have p0087 :=
    @g_sylibr (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I)))) p0072 p0086
  have p0088 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_csi (syn_cfrec F I))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I)))) p0070 p0087
  have p0089 :=
    @g_dmfco (syn_csn (.cv n)) (syn_ctcfn) (syn_csi (syn_cfrec F I))
  have p0090 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wfun (syn_csi (syn_cfrec F I))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I))))) (syn_wb (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))) (.classMem (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_cdm (syn_ctcfn)))) p0088 p0089
  have p0091 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))) (.classMem (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_cdm (syn_ctcfn))) p0058 p0090
  have p0092 :=
    @g_nntccl (.cv n)
  have p0093 :=
    @g_vex n
  have p0094 :=
    @g_tcfnfv (.cv n) p0093
  have p0095 :=
    @g_eleq1i (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n)) (syn_cdm (syn_cfrec G (syn_ctc I))) p0094
  have p0096 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_frecteqval_4 hyp_frecteqval_5 hyp_frecteqval_6
  have p0097 :=
    @g_eqid (syn_cfrec G (syn_ctc I))
  have p0098 :=
    @g_simp1 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))
  have p0099 :=
    @g_simp2 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))
  have p0100 :=
    @g_simp3 (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))
  have p0101 :=
    @g_fnfrec (syn_w3a (.classMem G (syn_cfuns)) (.classMem (syn_ctc I) (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))) (syn_cfrec G (syn_ctc I)) G (syn_ctc I) p0097 p0098 p0099 p0100
  have p0102 :=
    Nominal.mp p0096 p0101
  have p0103 :=
    @g_fndm (syn_cnnc) (syn_cfrec G (syn_ctc I))
  have p0104 :=
    Nominal.mp p0102 p0103
  have p0105 :=
    @g_eleq2i (syn_cdm (syn_cfrec G (syn_ctc I))) (syn_cnnc) (syn_ctc (.cv n)) p0104
  have p0106 :=
    @g_bitri (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec G (syn_ctc I)))) (.classMem (syn_ctc (.cv n)) (syn_cdm (syn_cfrec G (syn_ctc I)))) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0095 p0105
  have p0107 :=
    @g_sylibr (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec G (syn_ctc I)))) p0092 p0106
  have p0108 :=
    @g_fntcfn
  have p0109 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0110 :=
    Nominal.mp p0108 p0109
  have p0111 :=
    @g_vex n
  have p0112 :=
    @g_snel1c (.cv n) p0111
  have p0113 :=
    @g_fntcfn
  have p0114 :=
    @g_fndm (syn_c1c) (syn_ctcfn)
  have p0115 :=
    Nominal.mp p0113 p0114
  have p0116 :=
    @g_eleq2i (syn_cdm (syn_ctcfn)) (syn_c1c) (syn_csn (.cv n)) p0115
  have p0117 :=
    @g_mpbir (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn))) (.classMem (syn_csn (.cv n)) (syn_c1c)) p0112 p0116
  have p0118 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn))) p0110 p0117
  have p0119 :=
    @g_dmfco (syn_csn (.cv n)) (syn_cfrec G (syn_ctc I)) (syn_ctcfn)
  have p0120 :=
    Nominal.mp p0118 p0119
  have p0121 :=
    @g_sylibr (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec G (syn_ctc I)))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))) p0107 p0120
  have p0122 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))) p0091 p0121
  have p0123 :=
    @g_n_3jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_wfun (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))) (syn_wa (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) p0023 p0039 p0122
  have p0124 :=
    @g_funeqfix (syn_csn (.cv n)) (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))
  have p0125 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_w3a (syn_wfun (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_wfun (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))) (syn_wa (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))))) (syn_wb (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) (.classEq (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n))) (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n))))) p0123 p0124
  have p0126 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cfrecteq F G I)) (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I)))) (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn))))) (.classEq (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n))) (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n)))) p0005 p0125
  have p0127 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_frecteqval_1 hyp_frecteqval_2 hyp_frecteqval_3
  have p0128 :=
    @g_eqid (syn_cfrec F I)
  have p0129 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0130 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0131 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0132 :=
    @g_fnfrec (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0128 p0129 p0130 p0131
  have p0133 :=
    Nominal.mp p0127 p0132
  have p0134 :=
    @g_fnfun (syn_cnnc) (syn_cfrec F I)
  have p0135 :=
    Nominal.mp p0133 p0134
  have p0136 :=
    @g_funsi (syn_cfrec F I)
  have p0137 :=
    Nominal.mp p0135 p0136
  have p0138 :=
    @g_a1i (syn_wfun (syn_csi (syn_cfrec F I))) (.classMem (.cv n) (syn_cnnc)) p0137
  have p0139 :=
    @g_snelpw1 (.cv n) (syn_cnnc)
  have p0140 :=
    @g_biimpri (.classMem (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0139
  have p0141 :=
    @g_dmsi (syn_cfrec F I)
  have p0142 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_frecteqval_1 hyp_frecteqval_2 hyp_frecteqval_3
  have p0143 :=
    @g_eqid (syn_cfrec F I)
  have p0144 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0145 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0146 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0147 :=
    @g_fnfrec (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0143 p0144 p0145 p0146
  have p0148 :=
    Nominal.mp p0142 p0147
  have p0149 :=
    @g_fndm (syn_cnnc) (syn_cfrec F I)
  have p0150 :=
    Nominal.mp p0148 p0149
  have p0151 :=
    @g_pw1eq (syn_cdm (syn_cfrec F I)) (syn_cnnc)
  have p0152 :=
    Nominal.mp p0150 p0151
  have p0153 :=
    @g_eqtri (syn_cdm (syn_csi (syn_cfrec F I))) (syn_cpw1 (syn_cdm (syn_cfrec F I))) (syn_cpw1 (syn_cnnc)) p0141 p0152
  have p0154 :=
    @g_eleq2i (syn_cdm (syn_csi (syn_cfrec F I))) (syn_cpw1 (syn_cnnc)) (syn_csn (.cv n)) p0153
  have p0155 :=
    @g_sylibr (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I)))) p0140 p0154
  have p0156 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_csi (syn_cfrec F I))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I)))) p0138 p0155
  have p0157 :=
    @g_fvco (syn_csn (.cv n)) (syn_ctcfn) (syn_csi (syn_cfrec F I))
  have p0158 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wfun (syn_csi (syn_cfrec F I))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F I))))) (.classEq (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n))) (syn_cfv (syn_ctcfn) (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))))) p0156 p0157
  have p0159 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_frecteqval_1 hyp_frecteqval_2 hyp_frecteqval_3
  have p0160 :=
    @g_eqid (syn_cfrec F I)
  have p0161 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0162 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0163 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0164 :=
    @g_fnfrec (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0160 p0161 p0162 p0163
  have p0165 :=
    Nominal.mp p0159 p0164
  have p0166 :=
    @g_sifnvalv n (syn_cnnc) (syn_cfrec F I)
  have p0167 :=
    @g_mpan (syn_wfn (syn_cfrec F I) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n)))) p0165 p0166
  have p0168 :=
    @g_fveq2d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n))) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n))) (syn_ctcfn) p0167
  have p0169 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n))) (syn_cfv (syn_ctcfn) (syn_cfv (syn_csi (syn_cfrec F I)) (syn_csn (.cv n)))) (syn_cfv (syn_ctcfn) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n)))) p0158 p0168
  have p0170 :=
    @g_fvex (.cv n) (syn_cfrec F I)
  have p0171 :=
    @g_tcfnfv (syn_cfv (syn_cfrec F I) (.cv n)) p0170
  have p0172 :=
    @g_a1i (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n)))) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) p0171
  have p0173 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n))) (syn_cfv (syn_ctcfn) (syn_csn (syn_cfv (syn_cfrec F I) (.cv n)))) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) p0169 p0172
  have p0174 :=
    @g_fntcfn
  have p0175 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0176 :=
    Nominal.mp p0174 p0175
  have p0177 :=
    @g_vex n
  have p0178 :=
    @g_snel1c (.cv n) p0177
  have p0179 :=
    @g_fntcfn
  have p0180 :=
    @g_fndm (syn_c1c) (syn_ctcfn)
  have p0181 :=
    Nominal.mp p0179 p0180
  have p0182 :=
    @g_eleq2i (syn_cdm (syn_ctcfn)) (syn_c1c) (syn_csn (.cv n)) p0181
  have p0183 :=
    @g_mpbir (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn))) (.classMem (syn_csn (.cv n)) (syn_c1c)) p0178 p0182
  have p0184 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn))) p0176 p0183
  have p0185 :=
    @g_fvco (syn_csn (.cv n)) (syn_cfrec G (syn_ctc I)) (syn_ctcfn)
  have p0186 :=
    Nominal.mp p0184 p0185
  have p0187 :=
    @g_vex n
  have p0188 :=
    @g_tcfnfv (.cv n) p0187
  have p0189 :=
    @g_fveq2i (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n)) (syn_cfrec G (syn_ctc I)) p0188
  have p0190 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))) p0186 p0189
  have p0191 :=
    @g_a1i (.classEq (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n)))) (.classMem (.cv n) (syn_cnnc)) p0190
  have p0192 :=
    @g_eqeq12d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n))) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))) p0173 p0191
  have p0193 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cfrecteq F G I)) (.classEq (syn_cfv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))) (syn_csn (.cv n))) (syn_cfv (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)) (syn_csn (.cv n)))) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n)))) p0126 p0192
  exact p0193

noncomputable def g_frecteqvalcl
    (B : Class) (F : Class) (G : Class) (I : Class) (hyp_frecteqvalcl_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_frecteqvalcl_2 : Nominal.NPrf (.classMem I (syn_cdm F))) (hyp_frecteqvalcl_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_frecteqvalcl_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_frecteqvalcl_5 : Nominal.NPrf (.classMem (syn_ctc I) (syn_cdm G))) (hyp_frecteqvalcl_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B)) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B))))) := by
  let proofSupport : Finset Var := B.fv ∪ F.fv ∪ G.fv ∪ I.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_I : n ∉ I.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : n ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((Wff.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B)) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrecteq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem B (syn_cnnc))
  have p0001 :=
    @g_id (.classEq (.cv n) B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0003 :=
    @g_id (.classEq (.cv n) B)
  have p0004 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cfrecteq F G I) p0003
  have p0005 :=
    @g_id (.classEq (.cv n) B)
  have p0006 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec F I) p0005
  have p0007 :=
    @g_tceq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec F I) B)
  have p0008 :=
    @g_syl (.classEq (.cv n) B) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec F I) B)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) (syn_ctc (syn_cfv (syn_cfrec F I) B))) p0006 p0007
  have p0009 :=
    @g_id (.classEq (.cv n) B)
  have p0010 :=
    @g_tceq (.cv n) B
  have p0011 :=
    @g_syl (.classEq (.cv n) B) (.classEq (.cv n) B) (.classEq (syn_ctc (.cv n)) (syn_ctc B)) p0009 p0010
  have p0012 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_ctc (.cv n)) (syn_ctc B) (syn_cfrec G (syn_ctc I)) p0011
  have p0013 :=
    @g_eqeq12d (.classEq (.cv n) B) (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) (syn_ctc (syn_cfv (syn_cfrec F I) B)) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B)) p0008 p0012
  have p0014 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cfrecteq F G I)) (.classMem B (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n)))) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B)) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B))) p0004 p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n))))) (syn_wb (.classMem B (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B)) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B)))) p0002 p0014
  have p0016 :=
    @g_frecteqval n F G I hyp_frecteqvalcl_1 hyp_frecteqvalcl_2 hyp_frecteqvalcl_3 hyp_frecteqvalcl_4 hyp_frecteqvalcl_5 hyp_frecteqvalcl_6
  have p0017 :=
    @g_vtoclg (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc (.cv n)))))) (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B)) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B))))) n B (syn_cnnc) dv_cache_0001 dv_cache_0002 p0015 p0016
  have p0018 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cfrecteq F G I)) (.classEq (syn_ctc (syn_cfv (syn_cfrec F I) B)) (syn_cfv (syn_cfrec G (syn_ctc I)) (syn_ctc B)))) p0000 p0017
  exact p0018

#print axioms g_frecteqvalcl

end NFChoice.DirectNominalPrf.WPPReplay
