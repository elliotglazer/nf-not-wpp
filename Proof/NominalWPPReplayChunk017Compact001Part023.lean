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
import NominalWPPReplayChunk017Compact001Part022

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

noncomputable def g_hncodecmpsetssxpndv
    (A : Class) :
    Nominal.NPrf (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) := by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (h)
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_u_ne_c : u ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_u : c ≠ u :=
    Ne.symm fresh_u_ne_c
  have fresh_v_ne_c : v ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_v : c ≠ v :=
    Ne.symm fresh_v_ne_c
  have dv_cache_0001 : c ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ≠ c := by
    clear dv_cache_0001
    exact (show u ≠ c from (by exact fresh_u_ne_c))
  have dv_cache_0003 : v ≠ c := by
    clear dv_cache_0001 dv_cache_0002
    exact (show v ≠ c from (by exact fresh_v_ne_c))
  have dv_cache_0004 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0005 : Disjoint (A).fv ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (A).fv ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({c} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show c ∉ (A).fv from (by exact fresh_c_not_A))))))
  have dv_cache_0006 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : c ∉ ((syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_u, fresh_c_not_A, fresh_c_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((syn_chncodecmpset A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : v ∉ ((syn_chncodecmpset A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((syn_cxp (syn_chwcn A) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : v ∉ ((syn_cxp (syn_chwcn A) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))))
  have p0001 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_chncodecmpset A)) p0000
  have p0002 :=
    @g_brhncodecmpset c v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))) p0002
  have p0004 :=
    @g_hwnisohwisob v u A dv_cache_0004
  have p0005 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0004
  have p0006 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0007 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0005 p0006
  have p0008 :=
    @g_simpl (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))
  have p0009 :=
    @g_hwnisohwisob c u A dv_cache_0002
  have p0010 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv c))) p0009
  have p0011 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv c))
  have p0012 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv c))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A))) p0010 p0011
  have p0013 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A))
  have p0014 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0012 p0013
  have p0015 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (.classMem (.cv u) (syn_chwcn A)) p0008 p0014
  have p0016 :=
    @g_simpr (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))
  have p0017 :=
    @g_hncodecutreltargetclndv v A (.cv c) dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0018 :=
    @g_syl (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)) (.classMem (.cv v) (syn_chwcn A)) p0016 p0017
  have p0019 :=
    @g_jca (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0015 p0018
  have p0020 :=
    @g_exlimiv (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) c dv_cache_0008 p0019
  have p0021 :=
    @g_jaoi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))) p0007 p0020
  have p0022 :=
    @g_syl (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0003 p0021
  have p0023 :=
    @g_opelxp (.cv u) (.cv v) (syn_chwcn A) (syn_chwcn A)
  have p0024 :=
    @g_biimpri (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0023
  have p0025 :=
    @g_syl (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0022 p0024
  have p0026 :=
    @g_syl (.classMem (syn_cop (.cv u) (.cv v)) (syn_chncodecmpset A)) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0001 p0025
  have p0027 :=
    @g_relssi u v (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0004 p0026
  exact p0027

noncomputable def g_hncodecmpdefaultcnndv
    (A : Class) :
    Nominal.NPrf (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) := by
  let proofSupport : Finset Var := A.fv
  have dv_cache_0001 : Disjoint (A).fv ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv := by
    exact (show Disjoint (A).fv ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show Disjoint ((A).fv) ((((syn_ckqrel (syn_clefin))).fv) ∪ (((syn_cxp (syn_c0) (syn_c0))).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((syn_ckqrel (syn_clefin))).fv) from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel]; exact (show Disjoint ((A).fv) (((syn_clefin)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp)))))), (show Disjoint ((A).fv) (((syn_cxp (syn_c0) (syn_c0))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp]; exact (show Disjoint ((A).fv) ((((syn_c0)).fv) ∪ (((syn_c0)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((syn_c0)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp)))), (show Disjoint ((A).fv) (((syn_c0)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))⟩))))
  have p0000 :=
    @g_wecomparisondefaultemptywe
  have p0001 :=
    @g_n_0ss A
  have p0002 :=
    @g_pm3_2i (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wss (syn_c0) A) p0000 p0001
  have p0003 :=
    @g_wecomparisondefaultemptywe
  have p0004 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_simpli (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0005
  have p0007 :=
    @g_wecomparisondefaultemptywe
  have p0008 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_simpri (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0009
  have p0011 :=
    @g_elhwcodes A (syn_c0) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) dv_cache_0001 p0006 p0010
  have p0012 :=
    @g_biimpri (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcodes A)) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wss (syn_c0) A)) p0011
  have p0013 :=
    Nominal.mp p0002 p0012
  have p0014 :=
    @g_inss2 (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))
  have p0015 :=
    @g_wecomparisondefaultemptywe
  have p0016 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_simpli (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0017
  have p0019 :=
    @g_wecomparisondefaultemptywe
  have p0020 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_simpri (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0021
  have p0023 :=
    @g_opfv1st (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0018 p0022
  have p0024 :=
    @g_wecomparisondefaultemptywe
  have p0025 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_simpli (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0026
  have p0028 :=
    @g_wecomparisondefaultemptywe
  have p0029 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_simpri (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0030
  have p0032 :=
    @g_opfv2nd (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0027 p0031
  have p0033 :=
    @g_wecomparisondefaultemptywe
  have p0034 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0035 :=
    Nominal.mp p0033 p0034
  have p0036 :=
    @g_simpli (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0035
  have p0037 :=
    @g_wecomparisondefaultemptywe
  have p0038 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_simpri (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0039
  have p0041 :=
    @g_opfv2nd (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0036 p0040
  have p0042 :=
    @g_xpeq12i (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c0) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c0) p0032 p0041
  have p0043 :=
    @g_sseq12i (syn_cfv (syn_c1st) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cxp (syn_c0) (syn_c0)) p0023 p0042
  have p0044 :=
    @g_biimpri (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_wss (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cxp (syn_c0) (syn_c0))) p0043
  have p0045 :=
    Nominal.mp p0014 p0044
  have p0046 :=
    @g_pm3_2i (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) p0013 p0045
  have p0047 :=
    @g_wecomparisondefaultemptywe
  have p0048 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_simpli (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0049
  have p0051 :=
    @g_wecomparisondefaultemptywe
  have p0052 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0053 :=
    Nominal.mp p0051 p0052
  have p0054 :=
    @g_simpri (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0053
  have p0055 :=
    @g_opex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0050 p0054
  have p0056 :=
    @g_elhwcncl A (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0057 :=
    Nominal.mp p0055 p0056
  have p0058 :=
    @g_biimpri (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (syn_wa (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) p0057
  have p0059 :=
    Nominal.mp p0046 p0058
  exact p0059

noncomputable def g_hwcnweclndv
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B))) := by
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
  have dv_cache_0003 : u ∉ ((Wff.imp (.classMem B (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem B (syn_chwcn A))
  have p0001 :=
    @g_elex B (syn_chwcn A)
  have p0002 :=
    @g_id (.classEq (.cv u) B)
  have p0003 :=
    @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0002
  have p0004 :=
    @g_id (.classEq (.cv u) B)
  have p0005 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c1st) p0004
  have p0006 :=
    @g_id (.classEq (.cv u) B)
  have p0007 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0006
  have p0008 :=
    @g_breq12d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B) (syn_cwe) p0005 p0007
  have p0009 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A)) (.classMem B (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B)) p0003 p0008
  have p0010 :=
    @g_hwcnwendv u A dv_cache_0001
  have p0011 :=
    @g_vtoclg (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))) (.imp (.classMem B (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B))) u B (syn_cvv) dv_cache_0002 dv_cache_0003 p0009 p0010
  have p0012 :=
    @g_syl (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) (.imp (.classMem B (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B))) p0001 p0011
  have p0013 :=
    @g_mpd (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B)) p0000 p0012
  exact p0013

noncomputable def g_hwcnbaseclndv
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) B) A)) := by
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
  have dv_cache_0003 : u ∉ ((Wff.imp (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) B) A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem B (syn_chwcn A))
  have p0001 :=
    @g_elex B (syn_chwcn A)
  have p0002 :=
    @g_id (.classEq (.cv u) B)
  have p0003 :=
    @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0002
  have p0004 :=
    @g_id (.classEq (.cv u) B)
  have p0005 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0004
  have p0006 :=
    @g_sseq1d (.classEq (.cv u) B) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B) A p0005
  have p0007 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A)) (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A) (syn_wss (syn_cfv (syn_c2nd) B) A) p0003 p0006
  have p0008 :=
    @g_hwcnbase u A dv_cache_0001
  have p0009 :=
    @g_vtoclg (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) (.imp (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) B) A)) u B (syn_cvv) dv_cache_0002 dv_cache_0003 p0007 p0008
  have p0010 :=
    @g_syl (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) (.imp (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) B) A)) p0001 p0009
  have p0011 :=
    @g_mpd (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) B) A) p0000 p0010
  exact p0011

#print axioms g_hwcnbaseclndv

end NFChoice.DirectNominalPrf.WPPReplay
