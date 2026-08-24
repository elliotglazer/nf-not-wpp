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
import NominalWPPReplayChunk017Compact001Part010

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

noncomputable def g_hnsiquomapf1ndv
    (A : Class) (hyp_hnsiquomapf1ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (h)
  have fresh_q_ne_s : q ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_q : s ≠ q :=
    Ne.symm fresh_q_ne_s
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : s ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ≠ s := by
    clear dv_cache_0001 dv_cache_0002
    exact (show q ≠ s from (by exact fresh_q_ne_s))
  have dv_cache_0004 : s ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_chnord A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_q, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cpw1 (syn_chnord A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((syn_cpw1 (syn_chnord A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_chnsiquomap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : s ∉ ((syn_chnsiquomap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnsiquomapfndv A hyp_hnsiquomapf1ndv_1
  have p0001 :=
    @g_hnsiquomapfvineqndv A s q dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_hnsiquomapf1ndv_1
  have p0002 :=
    @g_ex (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))) p0001
  have p0003 :=
    @g_ralrimiv (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))) s (syn_cpw1 (syn_chnord A)) dv_cache_0004 p0002
  have p0004 :=
    @g_rgen (syn_wral s (syn_cpw1 (syn_chnord A)) (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))) q (syn_cpw1 (syn_chnord A)) p0003
  have p0005 :=
    @g_pm3_2i (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wral q (syn_cpw1 (syn_chnord A)) (syn_wral s (syn_cpw1 (syn_chnord A)) (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))))) p0000 p0004
  have p0006 :=
    @g_dff13 q s (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) (syn_chnsiquomap A) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0003
  have p0007_e01_recanon : Nominal.NPrf (syn_wb (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wa (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wral q (syn_cpw1 (syn_chnord A)) (syn_wral s (syn_cpw1 (syn_chnord A)) (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_chnsiquomap syn_cres syn_cpw1 syn_chnord syn_cqs syn_wrex syn_cec syn_cima syn_csn syn_chwcn syn_chwniso
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0007 :=
    @g_mpbir (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wa (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wral q (syn_cpw1 (syn_chnord A)) (syn_wral s (syn_cpw1 (syn_chnord A)) (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))))) p0005 p0007_e01_recanon
  exact p0007

noncomputable def g_hnsiquomapf1ondv
    (A : Class) (hyp_hnsiquomapf1ondv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf1o (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hnsiquomapf1ndv A hyp_hnsiquomapf1ondv_1
  have p0001 :=
    @g_hnsiquomapfondv A hyp_hnsiquomapf1ondv_1
  have p0002 :=
    @g_pm3_2i (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wfo (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))))
  have p0004 :=
    @g_mpbir (syn_wf1o (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wa (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wfo (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))) p0002 p0003
  exact p0004

noncomputable def g_hnordpw1shiftenndv
    (A : Class) (hyp_hnordpw1shiftenndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cpw1 (syn_chnord A)) (syn_cen) (syn_chnord (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hnsiquomapf1ondv A hyp_hnordpw1shiftenndv_1
  have p0001 :=
    @g_hnsiquomapexgndv A
  have p0002 :=
    Nominal.mp hyp_hnordpw1shiftenndv_1 p0001
  have p0003 :=
    @g_f1oen (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) (syn_chnsiquomap A) p0002
  have p0004 :=
    Nominal.mp p0000 p0003
  exact p0004

noncomputable def g_hncardtcshiftndv
    (A : Class) (hyp_hncardtcshiftndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_chncard A)) (syn_chncard (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hnordpw1shiftenndv A hyp_hncardtcshiftndv_1
  have p0001 :=
    @g_hncardtcshiftcondndv A hyp_hncardtcshiftndv_1 p0000
  exact p0001

noncomputable def g_wppconcrete6fntc7hncard1valndv
     :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_hncardtcshiftndv (syn_c1c) p0000
  have p0002 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard (syn_cpw1 (syn_c1c)))))
  have p0003 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_c1c))) (syn_chncard (syn_cpw1 (syn_c1c))) (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))) p0001 p0002
  have p0004 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c))))
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c))))))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))))))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c))))))))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))))))))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_fveq2i (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))))))))) (syn_cwppconcrete6fn) p0015
  have p0017 :=
    @g_n_1cex
  have p0018 :=
    @g_pw1ex (syn_c1c) p0017
  have p0019 :=
    @g_hnordexg (syn_cpw1 (syn_c1c))
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_wppconcrete6fnvalndv (syn_chnord (syn_cpw1 (syn_c1c))) p0020
  have p0022 :=
    @g_eqtri (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c))))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))) p0016 p0021
  exact p0022

#print axioms g_wppconcrete6fntc7hncard1valndv

end NFChoice.DirectNominalPrf.WPPReplay
