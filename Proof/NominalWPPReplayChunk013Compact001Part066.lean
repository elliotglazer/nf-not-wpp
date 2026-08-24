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
import NominalWPPReplayChunk013Compact001Part065

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

noncomputable def g_nnc3n3p2
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.neg (.classEq (syn_cplc (syn_cplc A A) A) (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_peano2 B
  have p0001 :=
    @g_nnc3n3p1 (syn_cplc B (syn_c1c)) A
  have p0002 :=
    @g_sylan (.classMem B (syn_cnnc)) (.classMem (syn_cplc B (syn_c1c)) (syn_cnnc)) (.classMem A (syn_cnnc)) (.neg (.classEq (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)))) p0000 p0001
  have p0003 :=
    @g_ancoms (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)) (.neg (.classEq (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)))) p0002
  have p0004 :=
    @g_eqcom (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c))
  have p0005 :=
    @g_addc4 B (syn_c1c) B (syn_c1c)
  have p0006 :=
    @g_addceq1i (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc B B) (syn_cplc (syn_c1c) (syn_c1c))) B p0005
  have p0007 :=
    @g_addc32 (syn_cplc B B) (syn_cplc (syn_c1c) (syn_c1c)) B
  have p0008 :=
    @g_n_1p1e2c
  have p0009 :=
    @g_addceq2i (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c) (syn_cplc (syn_cplc B B) B) p0008
  have p0010 :=
    @g_n_3eqtrri (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) B) (syn_cplc (syn_cplc (syn_cplc B B) (syn_cplc (syn_c1c) (syn_c1c))) B) (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_cplc (syn_c1c) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) p0006 p0007 p0009
  have p0011 :=
    @g_addceq1i (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) B) (syn_c1c) p0010
  have p0012 :=
    @g_addcass (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) B (syn_c1c)
  have p0013 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) B) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) (syn_cplc B (syn_c1c))) p0011 p0012
  have p0014 :=
    @g_eqeq1i (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)) p0013
  have p0015 :=
    @g_bitri (.classEq (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))) p0004 p0014
  have p0016 :=
    @g_sylnibr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c))) p0003 p0015
  have p0017 :=
    @g_nncaddccl A A
  have p0018 :=
    @g_anidms (.classMem A (syn_cnnc)) (.classMem (syn_cplc A A) (syn_cnnc)) p0017
  have p0019 :=
    @g_nncaddccl (syn_cplc A A) A
  have p0020 :=
    @g_mpancom (.classMem (syn_cplc A A) (syn_cnnc)) (.classMem A (syn_cnnc)) (.classMem (syn_cplc (syn_cplc A A) A) (syn_cnnc)) p0018 p0019
  have p0021 :=
    @g_nncaddccl B B
  have p0022 :=
    @g_anidms (.classMem B (syn_cnnc)) (.classMem (syn_cplc B B) (syn_cnnc)) p0021
  have p0023 :=
    @g_nncaddccl (syn_cplc B B) B
  have p0024 :=
    @g_mpancom (.classMem (syn_cplc B B) (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem (syn_cplc (syn_cplc B B) B) (syn_cnnc)) p0022 p0023
  have p0025 :=
    @g_n_2nnc
  have p0026 :=
    @g_nncaddccl (syn_cplc (syn_cplc B B) B) (syn_c2c)
  have p0027 :=
    @g_sylancl (.classMem B (syn_cnnc)) (.classMem (syn_cplc (syn_cplc B B) B) (syn_cnnc)) (.classMem (syn_c2c) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_cnnc)) p0024 p0025 p0026
  have p0028 :=
    @g_suc11nnc (syn_cplc (syn_cplc A A) A) (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c))
  have p0029 :=
    @g_syl2an (.classMem A (syn_cnnc)) (.classMem (syn_cplc (syn_cplc A A) A) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_cnnc)) (syn_wb (.classEq (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c))) (.classEq (syn_cplc (syn_cplc A A) A) (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)))) (.classMem B (syn_cnnc)) p0020 p0027 p0028
  have p0030 :=
    @g_mtbid (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c))) (.classEq (syn_cplc (syn_cplc A A) A) (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c))) p0016 p0029
  exact p0030

noncomputable def g_nchoicelem1
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))))) := by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have dv_cache_0001 : n ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((Wff.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nncdiv3 A n dv_cache_0001
  have p0001 :=
    @g_id (.classMem (.cv n) (syn_cnnc))
  have p0002 :=
    @g_nntccl (.cv n)
  have p0003 :=
    @g_nnc3n3p1 (.cv n) (syn_ctc (.cv n))
  have p0004 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) (.neg (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) (syn_c1c)))) p0001 p0002 p0003
  have p0005 :=
    @g_nncaddccl (.cv n) (.cv n)
  have p0006 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0005
  have p0007 :=
    @g_nnnc (syn_cplc (.cv n) (.cv n))
  have p0008 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cncs)) p0006 p0007
  have p0009 :=
    @g_nnnc (.cv n)
  have p0010 :=
    @g_tcdi (syn_cplc (.cv n) (.cv n)) (.cv n)
  have p0011 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cncs)) (.classMem (.cv n) (syn_cncs)) (.classEq (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_cplc (syn_ctc (syn_cplc (.cv n) (.cv n))) (syn_ctc (.cv n)))) p0008 p0009 p0010
  have p0012 :=
    @g_tcdi (.cv n) (.cv n)
  have p0013 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cncs)) (.classMem (.cv n) (syn_cncs)) (.classEq (syn_ctc (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n)))) p0009 p0009 p0012
  have p0014 :=
    @g_addceq1d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)) p0013
  have p0015 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_cplc (syn_ctc (syn_cplc (.cv n) (.cv n))) (syn_ctc (.cv n))) (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) p0011 p0014
  have p0016 :=
    @g_addceq1d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) (syn_c1c) p0015
  have p0017 :=
    @g_eqeq2d (.classMem (.cv n) (syn_cnnc)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) p0016
  have p0018 :=
    @g_mtbird (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) (syn_c1c))) p0004 p0017
  have p0019 :=
    @g_id (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
  have p0020 :=
    @g_tceq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0021 :=
    @g_addceq1d (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_ctc A) (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c) p0020
  have p0022 :=
    @g_eqeq12d (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_ctc A) (syn_c1c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c)) p0019 p0021
  have p0023 :=
    @g_notbid (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c))) p0022
  have p0024 :=
    @g_syl5ibrcom (.classMem (.cv n) (syn_cnnc)) (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.neg (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c)))) p0018 p0023
  have p0025 :=
    @g_nncaddccl (syn_cplc (.cv n) (.cv n)) (.cv n)
  have p0026 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc)) p0006 p0001 p0025
  have p0027 :=
    @g_nnnc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0028 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cncs)) p0026 p0027
  have p0029 :=
    @g_n_1cnc
  have p0030 :=
    @g_tcdi (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)
  have p0031 :=
    @g_sylancl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cncs)) (.classMem (syn_c1c) (syn_cncs)) (.classEq (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_ctc (syn_c1c)))) p0028 p0029 p0030
  have p0032 :=
    @g_tc1c
  have p0033 :=
    @g_a1i (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) (.classMem (.cv n) (syn_cnnc)) p0032
  have p0034 :=
    @g_addceq12d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) (syn_ctc (syn_c1c)) (syn_c1c) p0015 p0033
  have p0035 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_ctc (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) (syn_c1c)) p0031 p0034
  have p0036 :=
    @g_eqeq2d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) p0035
  have p0037 :=
    @g_mtbird (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) (syn_c1c))) p0004 p0036
  have p0038 :=
    @g_peano2 (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0039 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cnnc)) p0026 p0038
  have p0040 :=
    @g_nntccl (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0041 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cnnc)) (.classMem (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_cnnc)) p0039 p0040
  have p0042 :=
    @g_suc11nnc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
  have p0043 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc)) (.classMem (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_cnnc)) (syn_wb (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) p0026 p0041 p0042
  have p0044 :=
    @g_mtbird (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) p0037 p0043
  have p0045 :=
    @g_id (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
  have p0046 :=
    @g_tceq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0047 :=
    @g_addceq1d (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_ctc A) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_c1c) p0046
  have p0048 :=
    @g_eqeq12d (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cplc (syn_ctc A) (syn_c1c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_c1c)) p0045 p0047
  have p0049 :=
    @g_notbid (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_c1c))) p0048
  have p0050 :=
    @g_syl5ibrcom (.classMem (.cv n) (syn_cnnc)) (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.neg (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_c1c)))) p0044 p0049
  have p0051 :=
    @g_peano2 (.cv n)
  have p0052 :=
    @g_nntccl (syn_cplc (.cv n) (syn_c1c))
  have p0053 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (.classMem (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_cnnc)) p0051 p0052
  have p0054 :=
    @g_nnc3n3p2 (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (.cv n)
  have p0055 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.neg (.classEq (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) p0053 p0001 p0054
  have p0056 :=
    @g_n_2nnc
  have p0057 :=
    @g_nncaddccl (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)
  have p0058 :=
    @g_sylancl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc)) (.classMem (syn_c2c) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cnnc)) p0026 p0056 p0057
  have p0059 :=
    @g_nnnc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0060 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cncs)) p0058 p0059
  have p0061 :=
    @g_n_1cnc
  have p0062 :=
    @g_tcdi (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)
  have p0063 :=
    @g_sylancl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cncs)) (.classMem (syn_c1c) (syn_cncs)) (.classEq (syn_ctc (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c))) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_ctc (syn_c1c)))) p0060 p0061 p0062
  have p0064 :=
    @g_eqcomd (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c))) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_ctc (syn_c1c))) p0063
  have p0065 :=
    @g_tc1c
  have p0066 :=
    @g_addceq2i (syn_ctc (syn_c1c)) (syn_c1c) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0065
  have p0067 :=
    @g_addccom (syn_cplc (syn_c1c) (syn_c1c)) (.cv n)
  have p0068 :=
    @g_n_1p1e2c
  have p0069 :=
    @g_addceq2i (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c) (.cv n) p0068
  have p0070 :=
    @g_eqtr2i (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (.cv n)) (syn_cplc (.cv n) (syn_cplc (syn_c1c) (syn_c1c))) (syn_cplc (.cv n) (syn_c2c)) p0067 p0069
  have p0071 :=
    @g_addceq1i (syn_cplc (.cv n) (syn_c2c)) (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (.cv n)) (syn_c1c) p0070
  have p0072 :=
    @g_addcass (.cv n) (syn_c2c) (syn_c1c)
  have p0073 :=
    @g_addcass (syn_cplc (syn_c1c) (syn_c1c)) (.cv n) (syn_c1c)
  have p0074 :=
    @g_n_3eqtr3i (syn_cplc (syn_cplc (.cv n) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (.cv n)) (syn_c1c)) (syn_cplc (.cv n) (syn_cplc (syn_c2c) (syn_c1c))) (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) p0071 p0072 p0073
  have p0075 :=
    @g_addceq2i (syn_cplc (.cv n) (syn_cplc (syn_c2c) (syn_c1c))) (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (.cv n)) p0074
  have p0076 :=
    @g_addcass (syn_cplc (.cv n) (.cv n)) (.cv n) (syn_cplc (syn_c2c) (syn_c1c))
  have p0077 :=
    @g_addcass (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
  have p0078 :=
    @g_n_3eqtr4i (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv n) (syn_cplc (syn_c2c) (syn_c1c)))) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_c2c) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c))) p0075 p0076 p0077
  have p0079 :=
    @g_addcass (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c) (syn_c1c)
  have p0080 :=
    @g_addc4 (.cv n) (syn_c1c) (.cv n) (syn_c1c)
  have p0081 :=
    @g_addceq1i (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c)) p0080
  have p0082 :=
    @g_n_3eqtr4i (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_c2c) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c))) p0078 p0079 p0081
  have p0083 :=
    @g_tceq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c)))
  have p0084 :=
    Nominal.mp p0082 p0083
  have p0085 :=
    @g_n_3eqtr3g (.classMem (.cv n) (syn_cnnc)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_ctc (syn_c1c))) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c))) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c)))) p0064 p0066 p0084
  have p0086 :=
    @g_nnnc (syn_cplc (.cv n) (syn_c1c))
  have p0087 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)) p0051 p0086
  have p0088 :=
    @g_ncaddccl (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
  have p0089 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)) (.classMem (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cncs)) p0087 p0087 p0088
  have p0090 :=
    @g_tcdi (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c))
  have p0091 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cncs)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)) (.classEq (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) p0089 p0087 p0090
  have p0092 :=
    @g_tcdi (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
  have p0093 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)) (.classEq (syn_ctc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) p0087 p0087 p0092
  have p0094 :=
    @g_addceq1d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c))) p0093
  have p0095 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) p0091 p0094
  have p0096 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c)) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) p0085 p0095
  have p0097 :=
    @g_eqeq1d (.classMem (.cv n) (syn_cnnc)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c)) (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) p0096
  have p0098 :=
    @g_mtbird (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0055 p0097
  have p0099 :=
    @g_eqcom (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0100 :=
    @g_sylnib (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c))) p0098 p0099
  have p0101 :=
    @g_id (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
  have p0102 :=
    @g_tceq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0103 :=
    @g_addceq1d (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_ctc A) (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c) p0102
  have p0104 :=
    @g_eqeq12d (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cplc (syn_ctc A) (syn_c1c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c)) p0101 p0103
  have p0105 :=
    @g_notbid (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c))) p0104
  have p0106 :=
    @g_syl5ibrcom (.classMem (.cv n) (syn_cnnc)) (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.neg (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_c1c)))) p0100 p0105
  have p0107 :=
    @g_n_3jaod (.classMem (.cv n) (syn_cnnc)) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0024 p0050 p0106
  have p0108 :=
    @g_rexlimiv (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))) n (syn_cnnc) dv_cache_0002 p0107
  have p0109 :=
    @g_syl (.classMem A (syn_cnnc)) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))) p0000 p0108
  exact p0109

noncomputable def g_freceq12
    (F : Class) (G : Class) (I : Class) (J : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq F G) (.classEq I J)) (.classEq (syn_cfrec F I) (syn_cfrec G J))) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ I.fv ∪ J.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_J : x ∉ J.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (I).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (J).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_J, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_opeq2 I J (syn_c0c)
  have p0001 :=
    @g_sneqd (.classEq I J) (syn_cop (syn_c0c) I) (syn_cop (syn_c0c) J) p0000
  have p0002 :=
    @g_clos1eq1 (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F) (syn_csn (syn_cop (syn_c0c) I)) (syn_csn (syn_cop (syn_c0c) J))
  have p0003 :=
    @g_syl (.classEq I J) (.classEq (syn_csn (syn_cop (syn_c0c) I)) (syn_csn (syn_cop (syn_c0c) J))) (.classEq (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F)) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F))) p0001 p0002
  have p0004 :=
    @g_pprodeq2 F G (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))
  have p0005 :=
    @g_clos1eq2 (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F) (syn_csn (syn_cop (syn_c0c) J)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
  have p0006 :=
    @g_syl (.classEq F G) (.classEq (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) (.classEq (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F)) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))) p0004 p0005
  have p0007 :=
    @g_sylan9eqr (.classEq I J) (.classEq F G) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F)) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F)) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) p0003 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x F I dv_cache_0001 dv_cache_0002
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x G J dv_cache_0003 dv_cache_0004
  have p0010 :=
    @g_n_3eqtr4g (syn_wa (.classEq F G) (.classEq I J)) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F)) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) (syn_cfrec F I) (syn_cfrec G J) p0007 p0008 p0009
  exact p0010

#print axioms g_freceq12

end NFChoice.DirectNominalPrf.WPPReplay
