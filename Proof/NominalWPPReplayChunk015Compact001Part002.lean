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
import NominalWPPReplayChunk015Compact001Part001

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

noncomputable def g_hnwcutrelf
    (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutrelf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
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
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0002 : q ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_chwcn D)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_chnwcutrel R D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutrelfn D R hyp_hnwcutrelf_1
  have p0001 :=
    @g_hnwpw1argcl D q
  have p0002 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0001
  have p0003 :=
    @g_hnwcutcodecncl (syn_cuni (.cv q)) D R dv_cache_0001 hyp_hnwcutrelf_1
  have p0004 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D) (.classMem (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D)) p0002 p0003
  have p0005 :=
    @g_hnwcutrelval D R q hyp_hnwcutrelf_1
  have p0006 :=
    @g_eleq1d (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D) p0005
  have p0007 :=
    @g_mpbird (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D)) p0004 p0006
  have p0008 :=
    @g_rgen (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)) q (syn_cpw1 D) p0007
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (syn_wral q (syn_cpw1 D) (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D))) p0000 p0008
  have p0010 :=
    @g_ffnfv q (syn_cpw1 D) (syn_chwcn D) (syn_chnwcutrel R D) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0011 :=
    @g_mpbir (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) (syn_wa (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (syn_wral q (syn_cpw1 D) (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)))) p0009 p0010
  exact p0011

noncomputable def g_sifmap
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_ffn A B F
  have p0001 :=
    @g_fnfun A F
  have p0002 :=
    @g_syl (syn_wf F A B) (syn_wfn F A) (syn_wfun F) p0000 p0001
  have p0003 :=
    @g_funsi F
  have p0004 :=
    @g_syl (syn_wf F A B) (syn_wfun F) (syn_wfun (syn_csi F)) p0002 p0003
  have p0005 :=
    @g_funfn (syn_csi F)
  have p0006 :=
    @g_biimpi (syn_wfun (syn_csi F)) (syn_wfn (syn_csi F) (syn_cdm (syn_csi F))) p0005
  have p0007 :=
    @g_syl (syn_wf F A B) (syn_wfun (syn_csi F)) (syn_wfn (syn_csi F) (syn_cdm (syn_csi F))) p0004 p0006
  have p0008 :=
    @g_dmsi F
  have p0009 :=
    @g_a1i (.classEq (syn_cdm (syn_csi F)) (syn_cpw1 (syn_cdm F))) (syn_wf F A B) p0008
  have p0010 :=
    @g_ffn A B F
  have p0011 :=
    @g_fndm A F
  have p0012 :=
    @g_syl (syn_wf F A B) (syn_wfn F A) (.classEq (syn_cdm F) A) p0010 p0011
  have p0013 :=
    @g_pw1eq (syn_cdm F) A
  have p0014 :=
    @g_syl (syn_wf F A B) (.classEq (syn_cdm F) A) (.classEq (syn_cpw1 (syn_cdm F)) (syn_cpw1 A)) p0012 p0013
  have p0015 :=
    @g_eqtrd (syn_wf F A B) (syn_cdm (syn_csi F)) (syn_cpw1 (syn_cdm F)) (syn_cpw1 A) p0009 p0014
  have p0016 :=
    @g_fneq2d (syn_wf F A B) (syn_cdm (syn_csi F)) (syn_cpw1 A) (syn_csi F) p0015
  have p0017 :=
    @g_mpbid (syn_wf F A B) (syn_wfn (syn_csi F) (syn_cdm (syn_csi F))) (syn_wfn (syn_csi F) (syn_cpw1 A)) p0007 p0016
  have p0018 :=
    @g_frn A B F
  have p0019 :=
    @g_pw1ss (syn_crn F) B
  have p0020 :=
    @g_syl (syn_wf F A B) (syn_wss (syn_crn F) B) (syn_wss (syn_cpw1 (syn_crn F)) (syn_cpw1 B)) p0018 p0019
  have p0021 :=
    @g_rnsi F
  have p0022 :=
    @g_a1i (.classEq (syn_crn (syn_csi F)) (syn_cpw1 (syn_crn F))) (syn_wf F A B) p0021
  have p0023 :=
    @g_sseq1d (syn_wf F A B) (syn_crn (syn_csi F)) (syn_cpw1 (syn_crn F)) (syn_cpw1 B) p0022
  have p0024 :=
    @g_mpbird (syn_wf F A B) (syn_wss (syn_crn (syn_csi F)) (syn_cpw1 B)) (syn_wss (syn_cpw1 (syn_crn F)) (syn_cpw1 B)) p0020 p0023
  have p0025 :=
    @g_jca (syn_wf F A B) (syn_wfn (syn_csi F) (syn_cpw1 A)) (syn_wss (syn_crn (syn_csi F)) (syn_cpw1 B)) p0017 p0024
  have p0026 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))))
  have p0027 :=
    @g_sylibr (syn_wf F A B) (syn_wa (syn_wfn (syn_csi F) (syn_cpw1 A)) (syn_wss (syn_crn (syn_csi F)) (syn_cpw1 B))) (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) p0025 p0026
  exact p0027

noncomputable def g_sifvaldv
    (A : Class) (B : Class) (F : Class) (c : Var) (dv_A_c : c ∉ A.fv) (dv_B_c : c ∉ B.fv) (dv_F_c : c ∉ F.fv) (hyp_sifvaldv_1 : Nominal.NPrf (syn_wf F A B)) :
    Nominal.NPrf (.imp (.classMem (.cv c) A) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ ({c} : Finset Var)
  have p0000 :=
    @g_eqid (syn_cfv F (.cv c))
  have p0001 :=
    @g_a1i (.classEq (syn_cfv F (.cv c)) (syn_cfv F (.cv c))) (.classMem (.cv c) A) p0000
  have p0002 :=
    @g_ffn A B F
  have p0003 :=
    Nominal.mp hyp_sifvaldv_1 p0002
  have p0004 :=
    @g_a1i (syn_wfn F A) (.classMem (.cv c) A) p0003
  have p0005 :=
    @g_id (.classMem (.cv c) A)
  have p0006 :=
    @g_jca (.classMem (.cv c) A) (syn_wfn F A) (.classMem (.cv c) A) p0004 p0005
  have p0007 :=
    @g_fnbrfvb A (.cv c) (syn_cfv F (.cv c)) F
  have p0008 :=
    @g_syl (.classMem (.cv c) A) (syn_wa (syn_wfn F A) (.classMem (.cv c) A)) (syn_wb (.classEq (syn_cfv F (.cv c)) (syn_cfv F (.cv c))) (syn_wbr (.cv c) F (syn_cfv F (.cv c)))) p0006 p0007
  have p0009 :=
    @g_mpbid (.classMem (.cv c) A) (.classEq (syn_cfv F (.cv c)) (syn_cfv F (.cv c))) (syn_wbr (.cv c) F (syn_cfv F (.cv c))) p0001 p0008
  have p0010 :=
    @g_vex c
  have p0011 :=
    @g_fvex (.cv c) F
  have p0012 :=
    @g_brsnsi (.cv c) (syn_cfv F (.cv c)) F p0010 p0011
  have p0013 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (.cv c)) (syn_csi F) (syn_csn (syn_cfv F (.cv c)))) (syn_wbr (.cv c) F (syn_cfv F (.cv c)))) (.classMem (.cv c) A) p0012
  have p0014 :=
    @g_mpbird (.classMem (.cv c) A) (syn_wbr (syn_csn (.cv c)) (syn_csi F) (syn_csn (syn_cfv F (.cv c)))) (syn_wbr (.cv c) F (syn_cfv F (.cv c))) p0009 p0013
  have p0015 :=
    @g_sifmap A B F
  have p0016 :=
    Nominal.mp hyp_sifvaldv_1 p0015
  have p0017 :=
    @g_ffn (syn_cpw1 A) (syn_cpw1 B) (syn_csi F)
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_a1i (syn_wfn (syn_csi F) (syn_cpw1 A)) (.classMem (.cv c) A) p0018
  have p0020 :=
    @g_snelpw1 (.cv c) A
  have p0021 :=
    @g_biimpri (.classMem (syn_csn (.cv c)) (syn_cpw1 A)) (.classMem (.cv c) A) p0020
  have p0022 :=
    @g_jca (.classMem (.cv c) A) (syn_wfn (syn_csi F) (syn_cpw1 A)) (.classMem (syn_csn (.cv c)) (syn_cpw1 A)) p0019 p0021
  have p0023 :=
    @g_fnbrfvb (syn_cpw1 A) (syn_csn (.cv c)) (syn_csn (syn_cfv F (.cv c))) (syn_csi F)
  have p0024 :=
    @g_syl (.classMem (.cv c) A) (syn_wa (syn_wfn (syn_csi F) (syn_cpw1 A)) (.classMem (syn_csn (.cv c)) (syn_cpw1 A))) (syn_wb (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c)))) (syn_wbr (syn_csn (.cv c)) (syn_csi F) (syn_csn (syn_cfv F (.cv c))))) p0022 p0023
  have p0025 :=
    @g_mpbird (.classMem (.cv c) A) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c)))) (syn_wbr (syn_csn (.cv c)) (syn_csi F) (syn_csn (syn_cfv F (.cv c)))) p0014 p0024
  exact p0025

noncomputable def g_sifvald
    (A : Class) (B : Class) (C : Class) (F : Class) (hyp_sifvald_1 : Nominal.NPrf (syn_wf F A B)) :
    Nominal.NPrf (.imp (.classMem C A) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have dv_cache_0001 : c ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : c ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : c ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : c ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : c ∉ ((Wff.imp (.classMem C A) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, fresh_c_not_A, fresh_c_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex C A
  have p0001 :=
    @g_eleq1 (.cv c) C A
  have p0002 :=
    @g_sneq (.cv c) C
  have p0003 :=
    @g_fveq2d (.classEq (.cv c) C) (syn_csn (.cv c)) (syn_csn C) (syn_csi F) p0002
  have p0004 :=
    @g_fveq2 (.cv c) C F
  have p0005 :=
    @g_sneqd (.classEq (.cv c) C) (syn_cfv F (.cv c)) (syn_cfv F C) p0004
  have p0006 :=
    @g_eqeq12d (.classEq (.cv c) C) (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F (.cv c))) (syn_csn (syn_cfv F C)) p0003 p0005
  have p0007 :=
    @g_imbi12d (.classEq (.cv c) C) (.classMem (.cv c) A) (.classMem C A) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c)))) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))) p0001 p0006
  have p0008 :=
    @g_sifvaldv A B F c dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_sifvald_1
  have p0009 :=
    @g_vtoclg (.imp (.classMem (.cv c) A) (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))) (.imp (.classMem C A) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C)))) c C (syn_cvv) dv_cache_0004 dv_cache_0005 p0007 p0008
  have p0010 :=
    @g_mpcom (.classMem C (syn_cvv)) (.classMem C A) (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))) p0000 p0009
  exact p0010

noncomputable def g_hnqmap1valcl
    (A : Class) (B : Class) (hyp_hnqmap1valcl_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((Wff.imp (.classMem B (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex B (syn_chwcn A)
  have p0001 :=
    @g_eleq1 (.cv u) B (syn_chwcn A)
  have p0002 :=
    @g_sneq (.cv u) B
  have p0003 :=
    @g_fveq2d (.classEq (.cv u) B) (syn_csn (.cv u)) (syn_csn B) (syn_chnqmap1 A) p0002
  have p0004 :=
    @g_eceq1 (.cv u) B (syn_chwniso A)
  have p0005 :=
    @g_eqeq12d (.classEq (.cv u) B) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec (.cv u) (syn_chwniso A)) (syn_cec B (syn_chwniso A)) p0003 p0004
  have p0006 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A))) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A))) p0001 p0005
  have p0007 :=
    @g_hnqmap1val u A dv_cache_0001 hyp_hnqmap1valcl_1
  have p0008 :=
    @g_vtoclg (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)))) (.imp (.classMem B (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A)))) u B (syn_cvv) dv_cache_0002 dv_cache_0003 p0006 p0007
  have p0009 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A))) p0000 p0008
  exact p0009

noncomputable def g_qmapcompvald
    (ph : Wff) (A : Class) (B : Class) (G : Class) (X : Class) (p : Var) (hyp_qmapcompvald_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_qmapcompvald_2 : Nominal.NPrf (syn_wf G X (syn_cpw1 (syn_chwcn A)))) (hyp_qmapcompvald_3 : Nominal.NPrf (.imp ph (.classMem (.cv p) X))) (hyp_qmapcompvald_4 : Nominal.NPrf (.imp ph (.classEq (syn_cfv G (.cv p)) (syn_csn B)))) (hyp_qmapcompvald_5 : Nominal.NPrf (.imp ph (.classMem B (syn_chwcn A)))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) G) (.cv p)) (syn_cec B (syn_chwniso A)))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ G.fv ∪ X.fv ∪ ({p} : Finset Var)
  have p0000 :=
    @g_ffn X (syn_cpw1 (syn_chwcn A)) G
  have p0001 :=
    Nominal.mp hyp_qmapcompvald_2 p0000
  have p0002 :=
    @g_a1i (syn_wfn G X) ph p0001
  have p0003 :=
    @g_jca ph (syn_wfn G X) (.classMem (.cv p) X) p0002 hyp_qmapcompvald_3
  have p0004 :=
    @g_fvco2 X (.cv p) (syn_chnqmap1 A) G
  have p0005 :=
    @g_syl ph (syn_wa (syn_wfn G X) (.classMem (.cv p) X)) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) G) (.cv p)) (syn_cfv (syn_chnqmap1 A) (syn_cfv G (.cv p)))) p0003 p0004
  have p0006 :=
    @g_fveq2d ph (syn_cfv G (.cv p)) (syn_csn B) (syn_chnqmap1 A) hyp_qmapcompvald_4
  have p0007 :=
    @g_eqtrd ph (syn_cfv (syn_ccom (syn_chnqmap1 A) G) (.cv p)) (syn_cfv (syn_chnqmap1 A) (syn_cfv G (.cv p))) (syn_cfv (syn_chnqmap1 A) (syn_csn B)) p0005 p0006
  have p0008 :=
    @g_hnqmap1valcl A B hyp_qmapcompvald_1
  have p0009 :=
    @g_syl ph (.classMem B (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A))) hyp_qmapcompvald_5 p0008
  have p0010 :=
    @g_eqtrd ph (syn_cfv (syn_ccom (syn_chnqmap1 A) G) (.cv p)) (syn_cfv (syn_chnqmap1 A) (syn_csn B)) (syn_cec B (syn_chwniso A)) p0007 p0009
  exact p0010

noncomputable def g_hnwcutsirelf
    (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutsirelf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_csi (syn_chnwcutrel R D)) (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_chwcn D))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_hnwcutrelf D R dv_cache_0001 hyp_hnwcutsirelf_1
  have p0001 :=
    @g_sifmap (syn_cpw1 D) (syn_chwcn D) (syn_chnwcutrel R D)
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

noncomputable def g_hnwcutsirelex
    (D : Class) (R : Class) (hyp_hnwcutsirelex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_csi (syn_chnwcutrel R D)) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_hnwcutrelex D R hyp_hnwcutsirelex_1
  have p0001 :=
    @g_siex (syn_chnwcutrel R D) p0000
  exact p0001

noncomputable def g_hnwcutfactorf
    (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutfactorf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_brex R D (syn_cwe)
  have p0001 :=
    Nominal.mp hyp_hnwcutfactorf_1 p0000
  have p0002 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0001
  have p0003 :=
    @g_hnqmap1f D p0002
  have p0004 :=
    @g_hnwcutsirelf D R dv_cache_0001 hyp_hnwcutfactorf_1
  have p0005 :=
    @g_pm3_2i (syn_wf (syn_chnqmap1 D) (syn_cpw1 (syn_chwcn D)) (syn_chnord D)) (syn_wf (syn_csi (syn_chnwcutrel R D)) (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_chwcn D))) p0003 p0004
  have p0006 :=
    @g_fco (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_chwcn D)) (syn_chnord D) (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))
  have p0007 :=
    Nominal.mp p0005 p0006
  exact p0007

noncomputable def g_hnwcutrelvalcld
    (B : Class) (D : Class) (R : Class) (hyp_hnwcutrelvalcld_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem B D) (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn B)) (syn_chnwcutcode R D B))) := by
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
  have dv_cache_0001 : Disjoint ((syn_cuni (.cv x))).fv (R).fv := by
    exact (show Disjoint ((syn_cuni (.cv x))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv x)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))))
  have dv_cache_0002 : x ∉ ((syn_csn B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn B)) (syn_chnwcutcode R D B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem B D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutrelval D R x hyp_hnwcutrelvalcld_1
  have p0001 :=
    @g_rgen (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv x)) (syn_chnwcutcode R D (syn_cuni (.cv x)))) x (syn_cpw1 D) p0000
  have p0002 :=
    @g_snelpw1 B D
  have p0003 :=
    @g_biimpri (.classMem (syn_csn B) (syn_cpw1 D)) (.classMem B D) p0002
  have p0004 :=
    @g_simpr (.classMem B D) (.classEq (.cv x) (syn_csn B))
  have p0005 :=
    @g_fveq2d (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (.cv x) (syn_csn B) (syn_chnwcutrel R D) p0004
  have p0006 :=
    @g_simpr (.classMem B D) (.classEq (.cv x) (syn_csn B))
  have p0007 :=
    @g_unieqd (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (.cv x) (syn_csn B) p0006
  have p0008 :=
    @g_simpl (.classMem B D) (.classEq (.cv x) (syn_csn B))
  have p0009 :=
    @g_unisng B D
  have p0010 :=
    @g_syl (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (.classMem B D) (.classEq (syn_cuni (syn_csn B)) B) p0008 p0009
  have p0011 :=
    @g_eqtrd (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (syn_cuni (.cv x)) (syn_cuni (syn_csn B)) B p0007 p0010
  have p0012 :=
    @g_hnwcutcodeeq3 (syn_cuni (.cv x)) B D R dv_cache_0001
  have p0013 :=
    @g_syl (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (.classEq (syn_cuni (.cv x)) B) (.classEq (syn_chnwcutcode R D (syn_cuni (.cv x))) (syn_chnwcutcode R D B)) p0011 p0012
  have p0014 :=
    @g_eqeq12d (syn_wa (.classMem B D) (.classEq (.cv x) (syn_csn B))) (syn_cfv (syn_chnwcutrel R D) (.cv x)) (syn_cfv (syn_chnwcutrel R D) (syn_csn B)) (syn_chnwcutcode R D (syn_cuni (.cv x))) (syn_chnwcutcode R D B) p0005 p0013
  have p0015 :=
    @g_rspcdv (.classMem B D) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv x)) (syn_chnwcutcode R D (syn_cuni (.cv x)))) (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn B)) (syn_chnwcutcode R D B)) x (syn_csn B) (syn_cpw1 D) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0003 p0014
  have p0016 :=
    @g_mpi (.classMem B D) (syn_wral x (syn_cpw1 D) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv x)) (syn_chnwcutcode R D (syn_cuni (.cv x))))) (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn B)) (syn_chnwcutcode R D B)) p0001 p0015
  exact p0016

noncomputable def g_hnwcutsirelval
    (D : Class) (R : Class) (q : Var) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutsirelval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q)) (syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
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
    @g_hnwcutrelf D R dv_cache_0001 hyp_hnwcutsirelval_1
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
    @g_hnwcutrelvalcld (syn_cuni (syn_cuni (.cv q))) D R hyp_hnwcutsirelval_1
  have p0015 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0013 p0014
  have p0016 :=
    @g_sneqd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) p0015
  have p0017 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q)) (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0011 p0016
  exact p0017

noncomputable def g_hnwcutfactorval
    (D : Class) (R : Class) (q : Var) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutfactorval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_brex R D (syn_cwe)
  have p0001 :=
    Nominal.mp hyp_hnwcutfactorval_1 p0000
  have p0002 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0001
  have p0003 :=
    @g_hnwcutsirelf D R dv_cache_0001 hyp_hnwcutfactorval_1
  have p0004 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0005 :=
    @g_hnwcutsirelval D R q dv_cache_0001 hyp_hnwcutfactorval_1
  have p0006 :=
    @g_pw12argcl (.cv q) D
  have p0007 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0008 :=
    @g_hnwcutcodecncl (syn_cuni (syn_cuni (.cv q))) D R dv_cache_0001 hyp_hnwcutfactorval_1
  have p0009 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn D)) p0007 p0008
  have p0010 :=
    @g_qmapcompvald (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) D (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_csi (syn_chnwcutrel R D)) (syn_cpw1 (syn_cpw1 D)) q p0002 p0003 p0004 p0005 p0009
  exact p0010

noncomputable def g_hnwcutmapfactor
    (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutmapfactor_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classEq (syn_chnwcutmap R D) (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)))) := by
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
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_chnwcutmap R D)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutmapval D R q dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0001 :=
    @g_hnwcutfactorval D R q dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0002 :=
    @g_eqcomd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) p0001
  have p0003 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q)) p0000 p0002
  have p0004 :=
    @g_rgen (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q))) q (syn_cpw1 (syn_cpw1 D)) p0003
  have p0005 :=
    @g_hnwcutmapf D R dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0006 :=
    @g_ffn (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) (syn_chnwcutmap R D)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_hnwcutfactorf D R dv_cache_0001 hyp_hnwcutmapfactor_1
  have p0009 :=
    @g_ffn (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_pm3_2i (syn_wfn (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D))) (syn_wfn (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D))) p0007 p0010
  have p0012 :=
    @g_eqfnfv q (syn_cpw1 (syn_cpw1 D)) (syn_chnwcutmap R D) (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_mpbir (.classEq (syn_chnwcutmap R D) (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)))) (syn_wral q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (.cv q)))) p0004 p0013
  exact p0014

noncomputable def g_hnwcutmapex
    (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutmapex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_chnwcutmap R D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_hnwcutmapfactor D R dv_cache_0001 hyp_hnwcutmapex_1
  have p0001 :=
    @g_brex R D (syn_cwe)
  have p0002 :=
    Nominal.mp hyp_hnwcutmapex_1 p0001
  have p0003 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0004 :=
    @g_hnqmap1exg D
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_hnwcutsirelex D R hyp_hnwcutmapex_1
  have p0007 :=
    @g_coex (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D)) p0005 p0006
  have p0008 :=
    @g_eqeltri (syn_chnwcutmap R D) (syn_ccom (syn_chnqmap1 D) (syn_csi (syn_chnwcutrel R D))) (syn_cvv) p0000 p0007
  exact p0008

noncomputable def g_hnwcutmapcardle
    (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutmapcardle_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_chncard D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0002 : f ∉ ((syn_chnwcutmap R D)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_chnord D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutmapf1 D R dv_cache_0001 hyp_hnwcutmapcardle_1
  have p0001 :=
    @g_hnwcutmapex D R dv_cache_0001 hyp_hnwcutmapcardle_1
  have p0002 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) (.cv f) (syn_chnwcutmap R D)
  have p0003 :=
    @g_spcegv (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) (syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) f (syn_chnwcutmap R D) (syn_cvv) dv_cache_0002 dv_cache_0003 p0002
  have p0004 :=
    Nominal.mp p0001 p0003
  have p0005 :=
    Nominal.mp p0000 p0004
  have p0006 :=
    @g_brex R D (syn_cwe)
  have p0007 :=
    Nominal.mp hyp_hnwcutmapcardle_1 p0006
  have p0008 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0007
  have p0009 :=
    @g_pw1ex D p0008
  have p0010 :=
    @g_pw1ex (syn_cpw1 D) p0009
  have p0011 :=
    @g_brex R D (syn_cwe)
  have p0012 :=
    Nominal.mp hyp_hnwcutmapcardle_1 p0011
  have p0013 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0012
  have p0014 :=
    @g_hnordex D p0013
  have p0015 :=
    @g_nclenc (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) f dv_cache_0004 dv_cache_0005 p0010 p0014
  have p0016 :=
    @g_mpbir (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_cnc (syn_chnord D))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D))) p0005 p0015
  have p0017 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard D)))
  have p0018 :=
    @g_eqcomi (syn_chncard D) (syn_cnc (syn_chnord D)) p0017
  have p0019 :=
    @g_breq2i (syn_cnc (syn_chnord D)) (syn_chncard D) (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) p0018
  have p0020 :=
    @g_mpbi (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_cnc (syn_chnord D))) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_chncard D)) p0016 p0019
  exact p0020

noncomputable def g_hnwcutmaptc2le
    (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutmaptc2le_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wbr (syn_ctc (syn_ctc (syn_cnc D))) (syn_clec) (syn_chncard D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_hnwcutmapcardle D R dv_cache_0001 hyp_hnwcutmaptc2le_1
  have p0001 :=
    @g_brex R D (syn_cwe)
  have p0002 :=
    Nominal.mp hyp_hnwcutmaptc2le_1 p0001
  have p0003 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0004 :=
    @g_tc2nc D p0003
  have p0005 :=
    @g_breq1i (syn_ctc (syn_ctc (syn_cnc D))) (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_chncard D) (syn_clec) p0004
  have p0006 :=
    @g_mpbir (syn_wbr (syn_ctc (syn_ctc (syn_cnc D))) (syn_clec) (syn_chncard D)) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 D))) (syn_clec) (syn_chncard D)) p0000 p0005
  exact p0006

noncomputable def g_hwcnssbase
    (A : Class) (D : Class) (hyp_hwcnssbase_1 : Nominal.NPrf (syn_wss D A)) :
    Nominal.NPrf (syn_wss (syn_chwcn D) (syn_chwcn A)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (D).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact (show Disjoint (D).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint ((D).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((D).fv) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((D).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (D).fv from (by exact fresh_u_not_D)))))), (show Disjoint ((D).fv) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint ((D).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0002 : Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (A).fv from (by exact fresh_u_not_A)))))), (show Disjoint ((A).fv) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0003 : u ∉ ((syn_chwcn D)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hwcnraw u D
  have p0001 :=
    @g_hwcnpair u D
  have p0002 :=
    @g_eleq1d (.classMem (.cv u) (syn_chwcn D)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D) p0001
  have p0003 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcodes D)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)) p0000 p0002
  have p0004 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0005 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0006 :=
    @g_elhwcodes D (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001 p0004 p0005
  have p0007 :=
    @g_biimpi (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) p0006
  have p0008 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) p0003 p0007
  have p0009 :=
    @g_simpld (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) p0008
  have p0010 :=
    @g_hwcnraw u D
  have p0011 :=
    @g_hwcnpair u D
  have p0012 :=
    @g_eleq1d (.classMem (.cv u) (syn_chwcn D)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D) p0011
  have p0013 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcodes D)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)) p0010 p0012
  have p0014 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0015 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0016 :=
    @g_elhwcodes D (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001 p0014 p0015
  have p0017 :=
    @g_biimpi (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) p0016
  have p0018 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)) p0013 p0017
  have p0019 :=
    @g_simprd (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) p0018
  have p0020 :=
    @g_a1i (syn_wss D A) (.classMem (.cv u) (syn_chwcn D)) hyp_hwcnssbase_1
  have p0021 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn D)) (syn_cfv (syn_c2nd) (.cv u)) D A p0019 p0020
  have p0022 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A) p0009 p0021
  have p0023 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0024 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0025 :=
    @g_elhwcodes A (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0002 p0023 p0024
  have p0026 :=
    @g_biimpri (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) p0025
  have p0027 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)) p0022 p0026
  have p0028 :=
    @g_hwcnpair u D
  have p0029 :=
    @g_eleq1d (.classMem (.cv u) (syn_chwcn D)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A) p0028
  have p0030 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcodes A)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)) p0027 p0029
  have p0031 :=
    @g_hwcnsupp u D
  have p0032 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0030 p0031
  have p0033 :=
    @g_elhwcn u A
  have p0034 :=
    @g_biimpri (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0033
  have p0035 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) p0032 p0034
  have p0036 :=
    @g_ssriv u (syn_chwcn D) (syn_chwcn A) dv_cache_0003 dv_cache_0004 p0035
  exact p0036

#print axioms g_hwcnssbase

end NFChoice.DirectNominalPrf.WPPReplay
