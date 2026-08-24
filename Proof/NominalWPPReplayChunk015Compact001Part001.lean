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
import NominalWPPReplayChunk014Compact001

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

noncomputable def g_kqfinantinn
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (syn_wa (syn_wbr A (syn_ckqrel (syn_clefin)) B) (syn_wbr B (syn_ckqrel (syn_clefin)) A)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_kqlefinbr A B (syn_cnnc) (syn_cnnc)
  have p0001 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0002 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0003 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_kqlefinbr B A (syn_cnnc) (syn_cnnc)
  have p0005 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc))) (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk B A) (syn_clefin))) p0003 p0004
  have p0006 :=
    @g_anbi12d (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wbr A (syn_ckqrel (syn_clefin)) B) (.classMem (syn_copk A B) (syn_clefin)) (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk B A) (syn_clefin)) p0000 p0005
  have p0007 :=
    @g_biimpd (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (syn_wbr A (syn_ckqrel (syn_clefin)) B) (syn_wbr B (syn_ckqrel (syn_clefin)) A)) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) p0006
  have p0008 :=
    @g_lefinantinn A B
  have p0009 :=
    @g_syld (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (syn_wbr A (syn_ckqrel (syn_clefin)) B) (syn_wbr B (syn_ckqrel (syn_clefin)) A)) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) (.classEq A B) p0007 p0008
  exact p0009

noncomputable def g_nntctfin
    (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classEq (syn_ctc N) (syn_ctfin N))) := by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have dv_cache_0001 : a ∉ (N).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Wff.classEq (syn_ctc N) (syn_ctfin N))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Wff.classMem N (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem N (syn_cnnc))
  have p0001 :=
    @g_nulnnn
  have p0002 :=
    @g_eleq1 N (syn_c0) (syn_cnnc)
  have p0003 :=
    @g_mtbiri (.classEq N (syn_c0)) (.classMem N (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_necon2ai (.classMem N (syn_cnnc)) N (syn_c0) p0003
  have p0005 :=
    @g_jca (.classMem N (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) p0000 p0004
  have p0006 :=
    @g_tfinprop N a dv_cache_0001
  have p0007 :=
    @g_syl (.classMem N (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (syn_wa (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))) p0005 p0006
  have p0008 :=
    @g_simprd (.classMem N (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) p0007
  have p0009 :=
    @g_simpl (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))
  have p0010 :=
    @g_simpl (.classMem N (syn_cnnc)) (.classMem (.cv a) N)
  have p0011 :=
    @g_syl (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem N (syn_cnnc)) p0009 p0010
  have p0012 :=
    @g_nntccl N
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (.classMem N (syn_cnnc)) (.classMem (syn_ctc N) (syn_cnnc)) p0011 p0012
  have p0014 :=
    @g_simpl (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))
  have p0015 :=
    @g_simpl (.classMem N (syn_cnnc)) (.classMem (.cv a) N)
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem N (syn_cnnc)) p0014 p0015
  have p0017 :=
    @g_tfincl N
  have p0018 :=
    @g_syl (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (.classMem N (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) p0016 p0017
  have p0019 :=
    @g_jca (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (.classMem (syn_ctc N) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) p0013 p0018
  have p0020 :=
    @g_simpl (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))
  have p0021 :=
    @g_simpl (.classMem N (syn_cnnc)) (.classMem (.cv a) N)
  have p0022 :=
    @g_nnnc N
  have p0023 :=
    @g_syl (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem N (syn_cnnc)) (.classMem N (syn_cncs)) p0021 p0022
  have p0024 :=
    @g_simpr (.classMem N (syn_cnnc)) (.classMem (.cv a) N)
  have p0025 :=
    @g_jca (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem N (syn_cncs)) (.classMem (.cv a) N) p0023 p0024
  have p0026 :=
    @g_pw1eltc N (.cv a)
  have p0027 :=
    @g_syl (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (syn_wa (.classMem N (syn_cncs)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctc N)) p0025 p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctc N)) p0020 p0027
  have p0029 :=
    @g_simpr (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))
  have p0030 :=
    @g_jca (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (.classMem (syn_cpw1 (.cv a)) (syn_ctc N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)) p0028 p0029
  have p0031 :=
    @g_jca (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (syn_wa (.classMem (syn_ctc N) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc))) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctc N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) p0019 p0030
  have p0032 :=
    @g_nnceleq (syn_cpw1 (.cv a)) (syn_ctc N) (syn_ctfin N)
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (syn_wa (syn_wa (.classMem (syn_ctc N) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc))) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctc N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)))) (.classEq (syn_ctc N) (syn_ctfin N)) p0031 p0032
  have p0034 :=
    @g_ex (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv a) N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)) (.classEq (syn_ctc N) (syn_ctfin N)) p0033
  have p0035 :=
    @g_rexlimdva (.classMem N (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N)) (.classEq (syn_ctc N) (syn_ctfin N)) a N dv_cache_0002 dv_cache_0003 p0034
  have p0036 :=
    @g_mpd (.classMem N (syn_cnnc)) (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) (.classEq (syn_ctc N) (syn_ctfin N)) p0008 p0035
  exact p0036

noncomputable def g_tc6lecan
    (M : Class) (N : Class) (hyp_tc6lecb_1 : Nominal.NPrf (.classMem M (syn_cncs))) (hyp_tc6lecb_2 : Nominal.NPrf (.classMem N (syn_cncs))) :
    Nominal.NPrf (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wbr M (syn_clec) N)) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  have p0000 :=
    @g_tlecg M N
  have p0001 :=
    @g_mp2an (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wb (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N))) hyp_tc6lecb_1 hyp_tc6lecb_2 p0000
  have p0002 :=
    @g_tccl M
  have p0003 :=
    Nominal.mp hyp_tc6lecb_1 p0002
  have p0004 :=
    @g_tccl N
  have p0005 :=
    Nominal.mp hyp_tc6lecb_2 p0004
  have p0006 :=
    @g_tlecg (syn_ctc M) (syn_ctc N)
  have p0007 :=
    @g_mp2an (.classMem (syn_ctc M) (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) (syn_wb (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N)))) p0003 p0005 p0006
  have p0008 :=
    @g_bitri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N))) p0001 p0007
  have p0009 :=
    @g_tccl M
  have p0010 :=
    Nominal.mp hyp_tc6lecb_1 p0009
  have p0011 :=
    @g_tccl (syn_ctc M)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_tccl N
  have p0014 :=
    Nominal.mp hyp_tc6lecb_2 p0013
  have p0015 :=
    @g_tccl (syn_ctc N)
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_tlecg (syn_ctc (syn_ctc M)) (syn_ctc (syn_ctc N))
  have p0018 :=
    @g_mp2an (.classMem (syn_ctc (syn_ctc M)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) (syn_wb (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))) p0012 p0016 p0017
  have p0019 :=
    @g_bitri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0008 p0018
  have p0020 :=
    @g_tccl M
  have p0021 :=
    Nominal.mp hyp_tc6lecb_1 p0020
  have p0022 :=
    @g_tccl (syn_ctc M)
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_tccl (syn_ctc (syn_ctc M))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_tccl N
  have p0027 :=
    Nominal.mp hyp_tc6lecb_2 p0026
  have p0028 :=
    @g_tccl (syn_ctc N)
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_tccl (syn_ctc (syn_ctc N))
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    @g_tlecg (syn_ctc (syn_ctc (syn_ctc M))) (syn_ctc (syn_ctc (syn_ctc N)))
  have p0033 :=
    @g_mp2an (.classMem (syn_ctc (syn_ctc (syn_ctc M))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) (syn_wb (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0025 p0031 p0032
  have p0034 :=
    @g_bitri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0019 p0033
  have p0035 :=
    @g_tccl M
  have p0036 :=
    Nominal.mp hyp_tc6lecb_1 p0035
  have p0037 :=
    @g_tccl (syn_ctc M)
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_tccl (syn_ctc (syn_ctc M))
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc M)))
  have p0042 :=
    Nominal.mp p0040 p0041
  have p0043 :=
    @g_tccl N
  have p0044 :=
    Nominal.mp hyp_tc6lecb_2 p0043
  have p0045 :=
    @g_tccl (syn_ctc N)
  have p0046 :=
    Nominal.mp p0044 p0045
  have p0047 :=
    @g_tccl (syn_ctc (syn_ctc N))
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc N)))
  have p0050 :=
    Nominal.mp p0048 p0049
  have p0051 :=
    @g_tlecg (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))
  have p0052 :=
    @g_mp2an (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) (syn_wb (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0042 p0050 p0051
  have p0053 :=
    @g_bitri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0034 p0052
  have p0054 :=
    @g_tccl M
  have p0055 :=
    Nominal.mp hyp_tc6lecb_1 p0054
  have p0056 :=
    @g_tccl (syn_ctc M)
  have p0057 :=
    Nominal.mp p0055 p0056
  have p0058 :=
    @g_tccl (syn_ctc (syn_ctc M))
  have p0059 :=
    Nominal.mp p0057 p0058
  have p0060 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc M)))
  have p0061 :=
    Nominal.mp p0059 p0060
  have p0062 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))
  have p0063 :=
    Nominal.mp p0061 p0062
  have p0064 :=
    @g_tccl N
  have p0065 :=
    Nominal.mp hyp_tc6lecb_2 p0064
  have p0066 :=
    @g_tccl (syn_ctc N)
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_tccl (syn_ctc (syn_ctc N))
  have p0069 :=
    Nominal.mp p0067 p0068
  have p0070 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc N)))
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))
  have p0073 :=
    Nominal.mp p0071 p0072
  have p0074 :=
    @g_tlecg (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0075 :=
    @g_mp2an (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) (syn_wb (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) p0063 p0073 p0074
  have p0076 :=
    @g_bitri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0053 p0075
  have p0077 :=
    @g_biimpri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc M)))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0076
  exact p0077

noncomputable def g_tc2nc
    (A : Class) (hyp_tc2nc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A)))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_tcnc A hyp_tc2nc_1
  have p0001 :=
    @g_tceq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_pw1ex A hyp_tc2nc_1
  have p0004 :=
    @g_tcnc (syn_cpw1 A) p0003
  have p0005 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_cnc A))) (syn_ctc (syn_cnc (syn_cpw1 A))) (syn_cnc (syn_cpw1 (syn_cpw1 A))) p0002 p0004
  exact p0005

noncomputable def g_resiidima
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cima (syn_cres (syn_cid) A) B) (syn_cin A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_cnvresid A
  have p0001 :=
    @g_eqcomi (syn_ccnv (syn_cres (syn_cid) A)) (syn_cres (syn_cid) A) p0000
  have p0002 :=
    @g_imaeq1i (syn_cres (syn_cid) A) (syn_ccnv (syn_cres (syn_cid) A)) B p0001
  have p0003 :=
    @g_cnvresima A B (syn_cid)
  have p0004 :=
    @g_eqtri (syn_cima (syn_cres (syn_cid) A) B) (syn_cima (syn_ccnv (syn_cres (syn_cid) A)) B) (syn_cin (syn_cima (syn_ccnv (syn_cid)) B) A) p0002 p0003
  have p0005 :=
    @g_cnvi
  have p0006 :=
    @g_imaeq1i (syn_ccnv (syn_cid)) (syn_cid) B p0005
  have p0007 :=
    @g_imai B
  have p0008 :=
    @g_eqtri (syn_cima (syn_ccnv (syn_cid)) B) (syn_cima (syn_cid) B) B p0006 p0007
  have p0009 :=
    @g_ineq1i (syn_cima (syn_ccnv (syn_cid)) B) B A p0008
  have p0010 :=
    @g_eqtri (syn_cima (syn_cres (syn_cid) A) B) (syn_cin (syn_cima (syn_ccnv (syn_cid)) B) A) (syn_cin B A) p0004 p0009
  have p0011 :=
    @g_incom B A
  have p0012 :=
    @g_eqtri (syn_cima (syn_cres (syn_cid) A) B) (syn_cin B A) (syn_cin A B) p0010 p0011
  exact p0012

noncomputable def g_hnwsegfnex
    (D : Class) (R : Class) (hyp_hnwsegfnex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwsegfn R D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chnwsegfn] using (Nominal.classEqRefl (syn_chnwsegfn R D)))
  have p0001 :=
    @g_idex
  have p0002 :=
    @g_brex R D (syn_cwe)
  have p0003 :=
    Nominal.mp hyp_hnwsegfnex_1 p0002
  have p0004 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0003
  have p0005 :=
    @g_resex (syn_cid) D p0001 p0004
  have p0006 :=
    @g_imageex (syn_cres (syn_cid) D) p0005
  have p0007 :=
    @g_brex R D (syn_cwe)
  have p0008 :=
    Nominal.mp hyp_hnwsegfnex_1 p0007
  have p0009 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0008
  have p0010 :=
    @g_idex
  have p0011 :=
    @g_difex R (syn_cid) p0009 p0010
  have p0012 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0011
  have p0013 :=
    @g_imageex (syn_ccnv (syn_cdif R (syn_cid))) p0012
  have p0014 :=
    @g_coex (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) p0006 p0013
  have p0015 :=
    @g_eqeltri (syn_chnwsegfn R D) (syn_ccom (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) (syn_cvv) p0000 p0014
  exact p0015

noncomputable def g_hnwcodefnex
    (D : Class) (R : Class) (hyp_hnwcodefnex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwcodefn R) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chnwcodefn] using (Nominal.classEqRefl (syn_chnwcodefn R)))
  have p0001 :=
    @g_idex
  have p0002 :=
    @g_brex R D (syn_cwe)
  have p0003 :=
    Nominal.mp hyp_hnwcodefnex_1 p0002
  have p0004 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0003
  have p0005 :=
    @g_resex (syn_cid) R p0001 p0004
  have p0006 :=
    @g_imageex (syn_cres (syn_cid) R) p0005
  have p0007 :=
    @g_crossex
  have p0008 :=
    @g_idex
  have p0009 :=
    @g_idex
  have p0010 :=
    @g_txpex (syn_cid) (syn_cid) p0008 p0009
  have p0011 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)) p0007 p0010
  have p0012 :=
    @g_coex (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) p0006 p0011
  have p0013 :=
    @g_idex
  have p0014 :=
    @g_txpex (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid) p0012 p0013
  have p0015 :=
    @g_eqeltri (syn_chnwcodefn R) (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) (syn_cvv) p0000 p0014
  exact p0015

noncomputable def g_hnwcutfnex
    (D : Class) (R : Class) (hyp_hnwcutfnex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwcutfn R D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chnwcutfn] using (Nominal.classEqRefl (syn_chnwcutfn R D)))
  have p0001 :=
    @g_hnwcodefnex D R hyp_hnwcutfnex_1
  have p0002 :=
    @g_hnwsegfnex D R hyp_hnwcutfnex_1
  have p0003 :=
    @g_coex (syn_chnwcodefn R) (syn_chnwsegfn R D) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_chnwcutfn R D) (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_fvimagecl
    (B : Class) (F : Class) (hyp_fvimagecl_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_fvimagecl_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage F) B) (syn_cima F B)) := by
  let proofSupport : Finset Var := B.fv ∪ F.fv
  have p0000 :=
    @g_eqid (syn_cima F B)
  have p0001 :=
    @g_imaex F B hyp_fvimagecl_1 hyp_fvimagecl_2
  have p0002 :=
    @g_brimage B (syn_cima F B) F hyp_fvimagecl_2 p0001
  have p0003 :=
    @g_mpbir (syn_wbr B (syn_cimage F) (syn_cima F B)) (.classEq (syn_cima F B) (syn_cima F B)) p0000 p0002
  have p0004 :=
    @g_wppimagefn F hyp_fvimagecl_1
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage F) (syn_cvv)) (.classMem B (syn_cvv)) p0004 hyp_fvimagecl_2
  have p0006 :=
    @g_fnbrfvb (syn_cvv) B (syn_cima F B) (syn_cimage F)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_mpbir (.classEq (syn_cfv (syn_cimage F) B) (syn_cima F B)) (syn_wbr B (syn_cimage F) (syn_cima F B)) p0003 p0007
  exact p0008

noncomputable def g_fncovv
    (F : Class) (G : Class) (hyp_fncovv_1 : Nominal.NPrf (syn_wfn F (syn_cvv))) (hyp_fncovv_2 : Nominal.NPrf (syn_wfn G (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_ccom F G) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv
  have p0000 :=
    @g_ssv (syn_crn G)
  have p0001 :=
    @g_n_3pm3_2i (syn_wfn F (syn_cvv)) (syn_wfn G (syn_cvv)) (syn_wss (syn_crn G) (syn_cvv)) hyp_fncovv_1 hyp_fncovv_2 p0000
  have p0002 :=
    @g_fnco (syn_cvv) (syn_cvv) F G
  have p0003 :=
    Nominal.mp p0001 p0002
  exact p0003

noncomputable def g_fvtxpvv
    (A : Class) (F : Class) (G : Class) (hyp_fvtxpvv_1 : Nominal.NPrf (syn_wfn F (syn_cvv))) (hyp_fvtxpvv_2 : Nominal.NPrf (syn_wfn G (syn_cvv))) (hyp_fvtxpvv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_ctxp F G) A) (syn_cop (syn_cfv F A) (syn_cfv G A))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_eqid (syn_cfv F A)
  have p0001 :=
    @g_pm3_2i (syn_wfn F (syn_cvv)) (.classMem A (syn_cvv)) hyp_fvtxpvv_1 hyp_fvtxpvv_3
  have p0002 :=
    @g_fnbrfvb (syn_cvv) A (syn_cfv F A) F
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_mpbi (.classEq (syn_cfv F A) (syn_cfv F A)) (syn_wbr A F (syn_cfv F A)) p0000 p0003
  have p0005 :=
    @g_eqid (syn_cfv G A)
  have p0006 :=
    @g_pm3_2i (syn_wfn G (syn_cvv)) (.classMem A (syn_cvv)) hyp_fvtxpvv_2 hyp_fvtxpvv_3
  have p0007 :=
    @g_fnbrfvb (syn_cvv) A (syn_cfv G A) G
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbi (.classEq (syn_cfv G A) (syn_cfv G A)) (syn_wbr A G (syn_cfv G A)) p0005 p0008
  have p0010 :=
    @g_pm3_2i (syn_wbr A F (syn_cfv F A)) (syn_wbr A G (syn_cfv G A)) p0004 p0009
  have p0011 :=
    @g_trtxp A (syn_cfv F A) (syn_cfv G A) F G
  have p0012 :=
    @g_mpbir (syn_wbr A (syn_ctxp F G) (syn_cop (syn_cfv F A) (syn_cfv G A))) (syn_wa (syn_wbr A F (syn_cfv F A)) (syn_wbr A G (syn_cfv G A))) p0010 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn F (syn_cvv)) (syn_wfn G (syn_cvv)) hyp_fvtxpvv_1 hyp_fvtxpvv_2
  have p0014 :=
    @g_fntxp (syn_cvv) (syn_cvv) F G
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_inidm (syn_cvv)
  have p0017 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp F G) p0016
  have p0018 :=
    @g_mpbi (syn_wfn (syn_ctxp F G) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp F G) (syn_cvv)) p0015 p0017
  have p0019 :=
    @g_pm3_2i (syn_wfn (syn_ctxp F G) (syn_cvv)) (.classMem A (syn_cvv)) p0018 hyp_fvtxpvv_3
  have p0020 :=
    @g_fnbrfvb (syn_cvv) A (syn_cop (syn_cfv F A) (syn_cfv G A)) (syn_ctxp F G)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_mpbir (.classEq (syn_cfv (syn_ctxp F G) A) (syn_cop (syn_cfv F A) (syn_cfv G A))) (syn_wbr A (syn_ctxp F G) (syn_cop (syn_cfv F A) (syn_cfv G A))) p0012 p0021
  exact p0022

noncomputable def g_hnwsegfnfn
    (D : Class) (R : Class) (hyp_hnwsegfnfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwsegfn R D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_idex
  have p0001 :=
    @g_brex R D (syn_cwe)
  have p0002 :=
    Nominal.mp hyp_hnwsegfnfn_1 p0001
  have p0003 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0004 :=
    @g_resex (syn_cid) D p0000 p0003
  have p0005 :=
    @g_wppimagefn (syn_cres (syn_cid) D) p0004
  have p0006 :=
    @g_brex R D (syn_cwe)
  have p0007 :=
    Nominal.mp hyp_hnwsegfnfn_1 p0006
  have p0008 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0007
  have p0009 :=
    @g_idex
  have p0010 :=
    @g_difex R (syn_cid) p0008 p0009
  have p0011 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0010
  have p0012 :=
    @g_wppimagefn (syn_ccnv (syn_cdif R (syn_cid))) p0011
  have p0013 :=
    @g_fncovv (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) p0005 p0012
  have p0014 :=
    (by simpa [syn_chnwsegfn] using (Nominal.classEqRefl (syn_chnwsegfn R D)))
  have p0015 :=
    @g_fneq1i (syn_cvv) (syn_chnwsegfn R D) (syn_ccom (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) p0014
  have p0016 :=
    @g_mpbir (syn_wfn (syn_chnwsegfn R D) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) (syn_cvv)) p0013 p0015
  exact p0016

noncomputable def g_hnwcodefnfn
    (D : Class) (R : Class) (hyp_hnwcodefnfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwcodefn R) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_idex
  have p0001 :=
    @g_brex R D (syn_cwe)
  have p0002 :=
    Nominal.mp hyp_hnwcodefnfn_1 p0001
  have p0003 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0004 :=
    @g_resex (syn_cid) R p0000 p0003
  have p0005 :=
    @g_wppimagefn (syn_cres (syn_cid) R) p0004
  have p0006 :=
    @g_fncross
  have p0007 :=
    @g_fnresi (syn_cvv)
  have p0008 :=
    @g_resid (syn_cid)
  have p0009 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0008
  have p0010 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0007 p0009
  have p0011 :=
    @g_fnresi (syn_cvv)
  have p0012 :=
    @g_resid (syn_cid)
  have p0013 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0012
  have p0014 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0011 p0013
  have p0015 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0010 p0014
  have p0016 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cid)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_inidm (syn_cvv)
  have p0019 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cid)) p0018
  have p0020 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cvv)) p0017 p0019
  have p0021 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)) p0006 p0020
  have p0022 :=
    @g_fncovv (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) p0005 p0021
  have p0023 :=
    @g_fnresi (syn_cvv)
  have p0024 :=
    @g_resid (syn_cid)
  have p0025 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0024
  have p0026 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0023 p0025
  have p0027 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0022 p0026
  have p0028 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_inidm (syn_cvv)
  have p0031 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) p0030
  have p0032 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) (syn_cvv)) p0029 p0031
  have p0033 :=
    (by simpa [syn_chnwcodefn] using (Nominal.classEqRefl (syn_chnwcodefn R)))
  have p0034 :=
    @g_fneq1i (syn_cvv) (syn_chnwcodefn R) (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) p0033
  have p0035 :=
    @g_mpbir (syn_wfn (syn_chnwcodefn R) (syn_cvv)) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) (syn_cvv)) p0032 p0034
  exact p0035

noncomputable def g_hnwcutfnfn
    (D : Class) (R : Class) (hyp_hnwcutfnfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwcutfn R D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_hnwcodefnfn D R hyp_hnwcutfnfn_1
  have p0001 :=
    @g_hnwsegfnfn D R hyp_hnwcutfnfn_1
  have p0002 :=
    @g_fncovv (syn_chnwcodefn R) (syn_chnwsegfn R D) p0000 p0001
  have p0003 :=
    (by simpa [syn_chnwcutfn] using (Nominal.classEqRefl (syn_chnwcutfn R D)))
  have p0004 :=
    @g_fneq1i (syn_cvv) (syn_chnwcutfn R D) (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D)) p0003
  have p0005 :=
    @g_mpbir (syn_wfn (syn_chnwcutfn R D) (syn_cvv)) (syn_wfn (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D)) (syn_cvv)) p0002 p0004
  exact p0005

noncomputable def g_hnwsegfnval
    (B : Class) (D : Class) (R : Class) (hyp_hnwsegfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_hnwsegfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnwsegfnval_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chnwsegfn R D) B) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B))) := by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chnwsegfn] using (Nominal.classEqRefl (syn_chnwsegfn R D)))
  have p0001 :=
    @g_fveq1i B (syn_chnwsegfn R D) (syn_ccom (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) p0000
  have p0002 :=
    @g_idex
  have p0003 :=
    @g_difex R (syn_cid) hyp_hnwsegfnval_1 p0002
  have p0004 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0003
  have p0005 :=
    @g_wppimagefn (syn_ccnv (syn_cdif R (syn_cid))) p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) (syn_cvv)) (.classMem B (syn_cvv)) p0005 hyp_hnwsegfnval_3
  have p0007 :=
    @g_fvco2 (syn_cvv) B (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_eqtri (syn_cfv (syn_chnwsegfn R D) B) (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) B) (syn_cfv (syn_cimage (syn_cres (syn_cid) D)) (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)) p0001 p0008
  have p0010 :=
    @g_idex
  have p0011 :=
    @g_resex (syn_cid) D p0010 hyp_hnwsegfnval_2
  have p0012 :=
    @g_fvex B (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))
  have p0013 :=
    @g_fvimagecl (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B) (syn_cres (syn_cid) D) p0011 p0012
  have p0014 :=
    @g_eqtri (syn_cfv (syn_chnwsegfn R D) B) (syn_cfv (syn_cimage (syn_cres (syn_cid) D)) (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)) (syn_cima (syn_cres (syn_cid) D) (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)) p0009 p0013
  have p0015 :=
    @g_resiidima D (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)
  have p0016 :=
    @g_eqtri (syn_cfv (syn_chnwsegfn R D) B) (syn_cima (syn_cres (syn_cid) D) (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)) (syn_cin D (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)) p0014 p0015
  have p0017 :=
    @g_idex
  have p0018 :=
    @g_difex R (syn_cid) hyp_hnwsegfnval_1 p0017
  have p0019 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0018
  have p0020 :=
    @g_fvimagecl B (syn_ccnv (syn_cdif R (syn_cid))) p0019 hyp_hnwsegfnval_3
  have p0021 :=
    @g_ineq2i (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B) D p0020
  have p0022 :=
    @g_eqtri (syn_cfv (syn_chnwsegfn R D) B) (syn_cin D (syn_cfv (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) B)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)) p0016 p0021
  exact p0022

noncomputable def g_hnwcodefnval
    (B : Class) (R : Class) (hyp_hnwcodefnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_hnwcodefnval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chnwcodefn R) B) (syn_cop (syn_cin R (syn_cxp B B)) B)) := by
  let proofSupport : Finset Var := B.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chnwcodefn] using (Nominal.classEqRefl (syn_chnwcodefn R)))
  have p0001 :=
    @g_fveq1i B (syn_chnwcodefn R) (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) p0000
  have p0002 :=
    @g_idex
  have p0003 :=
    @g_resex (syn_cid) R p0002 hyp_hnwcodefnval_1
  have p0004 :=
    @g_wppimagefn (syn_cres (syn_cid) R) p0003
  have p0005 :=
    @g_fncross
  have p0006 :=
    @g_fnresi (syn_cvv)
  have p0007 :=
    @g_resid (syn_cid)
  have p0008 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0007
  have p0009 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0006 p0008
  have p0010 :=
    @g_fnresi (syn_cvv)
  have p0011 :=
    @g_resid (syn_cid)
  have p0012 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0011
  have p0013 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0009 p0013
  have p0015 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cid)
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_inidm (syn_cvv)
  have p0018 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cid)) p0017
  have p0019 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cvv)) p0016 p0018
  have p0020 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)) p0005 p0019
  have p0021 :=
    @g_fncovv (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) p0004 p0020
  have p0022 :=
    @g_fnresi (syn_cvv)
  have p0023 :=
    @g_resid (syn_cid)
  have p0024 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0023
  have p0025 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0022 p0024
  have p0026 :=
    @g_fvtxpvv B (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid) p0021 p0025 hyp_hnwcodefnval_2
  have p0027 :=
    @g_fncross
  have p0028 :=
    @g_fnresi (syn_cvv)
  have p0029 :=
    @g_resid (syn_cid)
  have p0030 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0029
  have p0031 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0028 p0030
  have p0032 :=
    @g_fnresi (syn_cvv)
  have p0033 :=
    @g_resid (syn_cid)
  have p0034 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0033
  have p0035 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0032 p0034
  have p0036 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0031 p0035
  have p0037 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cid)
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_inidm (syn_cvv)
  have p0040 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cid)) p0039
  have p0041 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cvv)) p0038 p0040
  have p0042 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)) p0027 p0041
  have p0043 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) (syn_cvv)) (.classMem B (syn_cvv)) p0042 hyp_hnwcodefnval_2
  have p0044 :=
    @g_fvco2 (syn_cvv) B (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))
  have p0045 :=
    Nominal.mp p0043 p0044
  have p0046 :=
    @g_fnresi (syn_cvv)
  have p0047 :=
    @g_resid (syn_cid)
  have p0048 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0047
  have p0049 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0046 p0048
  have p0050 :=
    @g_fnresi (syn_cvv)
  have p0051 :=
    @g_resid (syn_cid)
  have p0052 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0051
  have p0053 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0050 p0052
  have p0054 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0049 p0053
  have p0055 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cid)
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_inidm (syn_cvv)
  have p0058 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cid)) p0057
  have p0059 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cvv)) p0056 p0058
  have p0060 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cid) (syn_cid)) (syn_cvv)) (.classMem B (syn_cvv)) p0059 hyp_hnwcodefnval_2
  have p0061 :=
    @g_fvco2 (syn_cvv) B (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_fnresi (syn_cvv)
  have p0064 :=
    @g_resid (syn_cid)
  have p0065 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0064
  have p0066 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0063 p0065
  have p0067 :=
    @g_fnresi (syn_cvv)
  have p0068 :=
    @g_resid (syn_cid)
  have p0069 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0068
  have p0070 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0067 p0069
  have p0071 :=
    @g_fvtxpvv B (syn_cid) (syn_cid) p0066 p0070 hyp_hnwcodefnval_2
  have p0072 :=
    @g_fvi B (syn_cvv)
  have p0073 :=
    Nominal.mp hyp_hnwcodefnval_2 p0072
  have p0074 :=
    @g_fvi B (syn_cvv)
  have p0075 :=
    Nominal.mp hyp_hnwcodefnval_2 p0074
  have p0076 :=
    @g_opeq12i (syn_cfv (syn_cid) B) B (syn_cfv (syn_cid) B) B p0073 p0075
  have p0077 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cid) (syn_cid)) B) (syn_cop (syn_cfv (syn_cid) B) (syn_cfv (syn_cid) B)) (syn_cop B B) p0071 p0076
  have p0078 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cid) (syn_cid)) B) (syn_cop B B) (syn_ccross) p0077
  have p0079 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B) (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_cid) (syn_cid)) B)) (syn_cfv (syn_ccross) (syn_cop B B)) p0062 p0078
  have p0080 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co B (syn_ccross) B)))
  have p0081 :=
    @g_eqcomi (syn_co B (syn_ccross) B) (syn_cfv (syn_ccross) (syn_cop B B)) p0080
  have p0082 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B) (syn_cfv (syn_ccross) (syn_cop B B)) (syn_co B (syn_ccross) B) p0079 p0081
  have p0083 :=
    @g_pm3_2i (.classMem B (syn_cvv)) (.classMem B (syn_cvv)) hyp_hnwcodefnval_2 hyp_hnwcodefnval_2
  have p0084 :=
    @g_ovcross B B (syn_cvv) (syn_cvv)
  have p0085 :=
    Nominal.mp p0083 p0084
  have p0086 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B) (syn_co B (syn_ccross) B) (syn_cxp B B) p0082 p0085
  have p0087 :=
    @g_fveq2i (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B) (syn_cxp B B) (syn_cimage (syn_cres (syn_cid) R)) p0086
  have p0088 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B) (syn_cfv (syn_cimage (syn_cres (syn_cid) R)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) B)) (syn_cfv (syn_cimage (syn_cres (syn_cid) R)) (syn_cxp B B)) p0045 p0087
  have p0089 :=
    @g_idex
  have p0090 :=
    @g_resex (syn_cid) R p0089 hyp_hnwcodefnval_1
  have p0091 :=
    @g_xpex B B hyp_hnwcodefnval_2 hyp_hnwcodefnval_2
  have p0092 :=
    @g_fvimagecl (syn_cxp B B) (syn_cres (syn_cid) R) p0090 p0091
  have p0093 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B) (syn_cfv (syn_cimage (syn_cres (syn_cid) R)) (syn_cxp B B)) (syn_cima (syn_cres (syn_cid) R) (syn_cxp B B)) p0088 p0092
  have p0094 :=
    @g_resiidima R (syn_cxp B B)
  have p0095 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B) (syn_cima (syn_cres (syn_cid) R) (syn_cxp B B)) (syn_cin R (syn_cxp B B)) p0093 p0094
  have p0096 :=
    @g_fvi B (syn_cvv)
  have p0097 :=
    Nominal.mp hyp_hnwcodefnval_2 p0096
  have p0098 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B) (syn_cin R (syn_cxp B B)) (syn_cfv (syn_cid) B) B p0095 p0097
  have p0099 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) B) (syn_cop (syn_cfv (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) B) (syn_cfv (syn_cid) B)) (syn_cop (syn_cin R (syn_cxp B B)) B) p0026 p0098
  have p0100 :=
    @g_eqtri (syn_cfv (syn_chnwcodefn R) B) (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) B) (syn_cop (syn_cin R (syn_cxp B B)) B) p0001 p0099
  exact p0100

noncomputable def g_hnwcutfnvalg
    (B : Class) (D : Class) (R : Class) (hyp_hnwcutfnvalg_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_hnwcutfnvalg_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnwcutfnvalg_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chnwcutfn R D) B) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)))) := by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chnwcutfn] using (Nominal.classEqRefl (syn_chnwcutfn R D)))
  have p0001 :=
    @g_fveq1i B (syn_chnwcutfn R D) (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D)) p0000
  have p0002 :=
    @g_idex
  have p0003 :=
    @g_resex (syn_cid) D p0002 hyp_hnwcutfnvalg_2
  have p0004 :=
    @g_wppimagefn (syn_cres (syn_cid) D) p0003
  have p0005 :=
    @g_idex
  have p0006 :=
    @g_difex R (syn_cid) hyp_hnwcutfnvalg_1 p0005
  have p0007 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0006
  have p0008 :=
    @g_wppimagefn (syn_ccnv (syn_cdif R (syn_cid))) p0007
  have p0009 :=
    @g_fncovv (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) p0004 p0008
  have p0010 :=
    (by simpa [syn_chnwsegfn] using (Nominal.classEqRefl (syn_chnwsegfn R D)))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_chnwsegfn R D) (syn_ccom (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_chnwsegfn R D) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) (syn_cvv)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_chnwsegfn R D) (syn_cvv)) (.classMem B (syn_cvv)) p0012 hyp_hnwcutfnvalg_3
  have p0014 :=
    @g_fvco2 (syn_cvv) B (syn_chnwcodefn R) (syn_chnwsegfn R D)
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_chnwcutfn R D) B) (syn_cfv (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D)) B) (syn_cfv (syn_chnwcodefn R) (syn_cfv (syn_chnwsegfn R D) B)) p0001 p0015
  have p0017 :=
    @g_hnwsegfnval B D R hyp_hnwcutfnvalg_1 hyp_hnwcutfnvalg_2 hyp_hnwcutfnvalg_3
  have p0018 :=
    @g_fveq2i (syn_cfv (syn_chnwsegfn R D) B) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)) (syn_chnwcodefn R) p0017
  have p0019 :=
    @g_eqtri (syn_cfv (syn_chnwcutfn R D) B) (syn_cfv (syn_chnwcodefn R) (syn_cfv (syn_chnwsegfn R D) B)) (syn_cfv (syn_chnwcodefn R) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B))) p0016 p0018
  have p0020 :=
    @g_idex
  have p0021 :=
    @g_difex R (syn_cid) hyp_hnwcutfnvalg_1 p0020
  have p0022 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0021
  have p0023 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) B p0022 hyp_hnwcutfnvalg_3
  have p0024 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B) hyp_hnwcutfnvalg_2 p0023
  have p0025 :=
    @g_hnwcodefnval (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)) R hyp_hnwcutfnvalg_1 p0024
  have p0026 :=
    @g_eqtri (syn_cfv (syn_chnwcutfn R D) B) (syn_cfv (syn_chnwcodefn R) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) B))) p0019 p0025
  exact p0026

noncomputable def g_hnwcutfnvalcl
    (B : Class) (D : Class) (R : Class) (hyp_hnwcutfnvalcl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_hnwcutfnvalcl_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chnwcutfn R D) (syn_csn B)) (syn_chnwcutcode R D B)) := by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_brex R D (syn_cwe)
  have p0001 :=
    Nominal.mp hyp_hnwcutfnvalcl_1 p0000
  have p0002 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0001
  have p0003 :=
    @g_brex R D (syn_cwe)
  have p0004 :=
    Nominal.mp hyp_hnwcutfnvalcl_1 p0003
  have p0005 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0004
  have p0006 :=
    @g_snex B
  have p0007 :=
    @g_hnwcutfnvalg (syn_csn B) D R p0002 p0005 p0006
  have p0008 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D B)))
  have p0009 :=
    @g_eqcomi (syn_chnwcutcode R D B) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) p0008
  have p0010 :=
    @g_eqtri (syn_cfv (syn_chnwcutfn R D) (syn_csn B)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_chnwcutcode R D B) p0007 p0009
  exact p0010

noncomputable def g_hnwcutrelex
    (D : Class) (R : Class) (hyp_hnwcutrelex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwcutrel R D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chnwcutrel] using (Nominal.classEqRefl (syn_chnwcutrel R D)))
  have p0001 :=
    @g_hnwcutfnex D R hyp_hnwcutrelex_1
  have p0002 :=
    @g_brex R D (syn_cwe)
  have p0003 :=
    Nominal.mp hyp_hnwcutrelex_1 p0002
  have p0004 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0003
  have p0005 :=
    @g_pw1ex D p0004
  have p0006 :=
    @g_resex (syn_chnwcutfn R D) (syn_cpw1 D) p0001 p0005
  have p0007 :=
    @g_eqeltri (syn_chnwcutrel R D) (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (syn_cvv) p0000 p0006
  exact p0007

noncomputable def g_hnwcutrelfn
    (D : Class) (R : Class) (hyp_hnwcutrelfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_hnwcutfnfn D R hyp_hnwcutrelfn_1
  have p0001 :=
    @g_ssv (syn_cpw1 D)
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_chnwcutfn R D) (syn_cvv)) (syn_wss (syn_cpw1 D) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_fnssres (syn_cvv) (syn_cpw1 D) (syn_chnwcutfn R D)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    (by simpa [syn_chnwcutrel] using (Nominal.classEqRefl (syn_chnwcutrel R D)))
  have p0006 :=
    @g_fneq1i (syn_cpw1 D) (syn_chnwcutrel R D) (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (syn_wfn (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (syn_cpw1 D)) p0004 p0006
  exact p0007

noncomputable def g_hnwpw1argcl
    (D : Class) (q : Var) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))) := by
  let proofSupport : Finset Var := D.fv ∪ ({q} : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_q : x ≠ q := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have dv_cache_0001 : x ∉ ((Class.cv q)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_q, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elpw1 x (.cv q) D dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv q) (syn_cpw1 D)) (syn_wrex x D (.classEq (.cv q) (syn_csn (.cv x)))) p0000
  have p0002 :=
    @g_simpr (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))
  have p0003 :=
    @g_id (.classEq (.cv q) (syn_csn (.cv x)))
  have p0004 :=
    @g_unieqd (.classEq (.cv q) (syn_csn (.cv x))) (.cv q) (syn_csn (.cv x)) p0003
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_unisn (.cv x) p0005
  have p0007 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv x))) (.cv x)) (.classEq (.cv q) (syn_csn (.cv x))) p0006
  have p0008 :=
    @g_eqtrd (.classEq (.cv q) (syn_csn (.cv x))) (syn_cuni (.cv q)) (syn_cuni (syn_csn (.cv x))) (.cv x) p0004 p0007
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))) (.classEq (.cv q) (syn_csn (.cv x))) (.classEq (syn_cuni (.cv q)) (.cv x)) p0002 p0008
  have p0010 :=
    @g_simpl (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))
  have p0011 :=
    @g_eqeltrd (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))) (syn_cuni (.cv q)) (.cv x) D p0009 p0010
  have p0012 :=
    @g_simpr (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))
  have p0013 :=
    @g_simpr (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))
  have p0014 :=
    @g_id (.classEq (.cv q) (syn_csn (.cv x)))
  have p0015 :=
    @g_unieqd (.classEq (.cv q) (syn_csn (.cv x))) (.cv q) (syn_csn (.cv x)) p0014
  have p0016 :=
    @g_vex x
  have p0017 :=
    @g_unisn (.cv x) p0016
  have p0018 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv x))) (.cv x)) (.classEq (.cv q) (syn_csn (.cv x))) p0017
  have p0019 :=
    @g_eqtrd (.classEq (.cv q) (syn_csn (.cv x))) (syn_cuni (.cv q)) (syn_cuni (syn_csn (.cv x))) (.cv x) p0015 p0018
  have p0020 :=
    @g_syl (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))) (.classEq (.cv q) (syn_csn (.cv x))) (.classEq (syn_cuni (.cv q)) (.cv x)) p0013 p0019
  have p0021 :=
    @g_sneqd (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))) (syn_cuni (.cv q)) (.cv x) p0020
  have p0022 :=
    @g_eqcomd (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))) (syn_csn (syn_cuni (.cv q))) (syn_csn (.cv x)) p0021
  have p0023 :=
    @g_eqtrd (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))) (.cv q) (syn_csn (.cv x)) (syn_csn (syn_cuni (.cv q))) p0012 p0022
  have p0024 :=
    @g_jca (syn_wa (.classMem (.cv x) D) (.classEq (.cv q) (syn_csn (.cv x)))) (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0011 p0023
  have p0025 :=
    @g_rexlimiva (.classEq (.cv q) (syn_csn (.cv x))) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) x D dv_cache_0003 p0024
  have p0026 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 D)) (syn_wrex x D (.classEq (.cv q) (syn_csn (.cv x)))) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0001 p0025
  exact p0026

noncomputable def g_hnwcutrelval
    (D : Class) (R : Class) (q : Var) (hyp_hnwcutrelval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chnwcutcode R D (syn_cuni (.cv q))))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({q} : Finset Var)
  have p0000 :=
    (by simpa [syn_chnwcutrel] using (Nominal.classEqRefl (syn_chnwcutrel R D)))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_chnwcutrel R D) (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_cfv (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (.cv q))) (.classMem (.cv q) (syn_cpw1 D)) p0001
  have p0003 :=
    @g_fvres (.cv q) (syn_cpw1 D) (syn_chnwcutfn R D)
  have p0004 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_cfv (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (.cv q)) (syn_cfv (syn_chnwcutfn R D) (.cv q)) p0002 p0003
  have p0005 :=
    @g_hnwpw1argcl D q
  have p0006 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005
  have p0007 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 D)) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnwcutfn R D) p0006
  have p0008 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_cfv (syn_chnwcutfn R D) (.cv q)) (syn_cfv (syn_chnwcutfn R D) (syn_csn (syn_cuni (.cv q)))) p0004 p0007
  have p0009 :=
    @g_vex q
  have p0010 :=
    @g_uniex (.cv q) p0009
  have p0011 :=
    @g_hnwcutfnvalcl (syn_cuni (.cv q)) D R hyp_hnwcutrelval_1 p0010
  have p0012 :=
    @g_a1i (.classEq (syn_cfv (syn_chnwcutfn R D) (syn_csn (syn_cuni (.cv q)))) (syn_chnwcutcode R D (syn_cuni (.cv q)))) (.classMem (.cv q) (syn_cpw1 D)) p0011
  have p0013 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_cfv (syn_chnwcutfn R D) (syn_csn (syn_cuni (.cv q)))) (syn_chnwcutcode R D (syn_cuni (.cv q))) p0008 p0012
  exact p0013

#print axioms g_hnwcutrelval

end NFChoice.DirectNominalPrf.WPPReplay
