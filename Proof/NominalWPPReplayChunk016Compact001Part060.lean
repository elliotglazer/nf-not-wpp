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
import NominalWPPReplayChunk016Compact001Part059

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

noncomputable def g_wpppowset2imssndv
    (C : Class) (Q : Class) (hyp_wpppowset2imssndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) (hyp_wpppowset2imssndv_2 : Nominal.NPrf (syn_wss Q (syn_cnc C))) :
    Nominal.NPrf (syn_wss (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) (syn_cnc (syn_cpw (syn_cpw C)))) := by
  let proofSupport : Finset Var := C.fv ∪ Q.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_Q : y ∉ Q.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_Q : x ∉ Q.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((syn_cpw1 (syn_cpw1 Q))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cwpppowset2fn)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowset2fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (Q).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) (syn_cnc (syn_cpw (syn_cpw C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowset2fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cnc (syn_cpw (syn_cpw C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wpppowset2fnfnndv
  have p0001 :=
    @g_ssv (syn_cpw1 Q)
  have p0002 :=
    @g_pw1ss (syn_cpw1 Q) (syn_cvv)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cwpppowset2fn) (syn_cpw1 (syn_cvv))) (syn_wss (syn_cpw1 (syn_cpw1 Q)) (syn_cpw1 (syn_cvv))) p0000 p0003
  have p0005 :=
    @g_fvelimab x (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cpw1 Q)) (.cv y) (syn_cwpppowset2fn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_biimpi (.classMem (.cv y) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))) (syn_wrex x (syn_cpw1 (syn_cpw1 Q)) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) p0006
  have p0008 :=
    @g_simpr (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))
  have p0009 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))
  have p0010 :=
    @g_ssv Q
  have p0011 :=
    @g_pw1ss Q (syn_cvv)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_pw1ss (syn_cpw1 Q) (syn_cpw1 (syn_cvv))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_sseli (syn_cpw1 (syn_cpw1 Q)) (syn_cpw1 (syn_cpw1 (syn_cvv))) (.cv x) p0014
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classMem (.cv x) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0009 p0015
  have p0017 :=
    @g_wpppowset2fnvalimpndv x
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (.classMem (.cv x) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x)))))) p0016 p0017
  have p0019 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))
  have p0020 :=
    @g_fdcolcodearg Q x dv_cache_0004
  have p0021 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) Q) (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))) p0019 p0020
  have p0022 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv x))) Q) (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))
  have p0023 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) Q) (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))) (.classMem (syn_cuni (syn_cuni (.cv x))) Q) p0021 p0022
  have p0024 :=
    @g_sseli Q (syn_cnc C) (syn_cuni (syn_cuni (.cv x))) hyp_wpppowset2imssndv_2
  have p0025 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (.classMem (syn_cuni (syn_cuni (.cv x))) Q) (.classMem (syn_cuni (syn_cuni (.cv x))) (syn_cnc C)) p0023 p0024
  have p0026 :=
    @g_elnc (syn_cuni (syn_cuni (.cv x))) C
  have p0027 :=
    @g_sylib (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (.classMem (syn_cuni (syn_cuni (.cv x))) (syn_cnc C)) (syn_wbr (syn_cuni (syn_cuni (.cv x))) (syn_cen) C) p0025 p0026
  have p0028 :=
    @g_enpw (syn_cuni (syn_cuni (.cv x))) C
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (syn_wbr (syn_cuni (syn_cuni (.cv x))) (syn_cen) C) (syn_wbr (syn_cpw (syn_cuni (syn_cuni (.cv x)))) (syn_cen) (syn_cpw C)) p0027 p0028
  have p0030 :=
    @g_enpw (syn_cpw (syn_cuni (syn_cuni (.cv x)))) (syn_cpw C)
  have p0031 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (syn_wbr (syn_cpw (syn_cuni (syn_cuni (.cv x)))) (syn_cen) (syn_cpw C)) (syn_wbr (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))) (syn_cen) (syn_cpw (syn_cpw C))) p0029 p0030
  have p0032 :=
    @g_elnc (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))) (syn_cpw (syn_cpw C))
  have p0033 :=
    @g_sylibr (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (syn_wbr (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))) (syn_cen) (syn_cpw (syn_cpw C))) (.classMem (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))) (syn_cnc (syn_cpw (syn_cpw C)))) p0031 p0032
  have p0034 :=
    @g_eqeltrd (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (syn_cfv (syn_cwpppowset2fn) (.cv x)) (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))) (syn_cnc (syn_cpw (syn_cpw C))) p0018 p0033
  have p0035 :=
    @g_eqeltrrd (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q))) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y) (syn_cnc (syn_cpw (syn_cpw C))) p0008 p0034
  have p0036 :=
    @g_rexlimiva (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)) (.classMem (.cv y) (syn_cnc (syn_cpw (syn_cpw C)))) x (syn_cpw1 (syn_cpw1 Q)) dv_cache_0005 p0035
  have p0037 :=
    @g_syl (.classMem (.cv y) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))) (syn_wrex x (syn_cpw1 (syn_cpw1 Q)) (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))) (.classMem (.cv y) (syn_cnc (syn_cpw (syn_cpw C)))) p0007 p0036
  have p0038 :=
    @g_ssriv y (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) (syn_cnc (syn_cpw (syn_cpw C))) dv_cache_0006 dv_cache_0007 p0037
  exact p0038

noncomputable def g_sif1mapndv
    (A : Class) (B : Class) (F : Class) (hyp_sif1mapndv_1 : Nominal.NPrf (syn_wf1 F A B)) :
    Nominal.NPrf (syn_wf1 (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1f A B F
  have p0001 :=
    Nominal.mp hyp_sif1mapndv_1 p0000
  have p0002 :=
    @g_sifmap A B F
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A B)))
  have p0005 :=
    @g_mpbi (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))) hyp_sif1mapndv_1 p0004
  have p0006 :=
    @g_simpri (syn_wf F A B) (syn_wfun (syn_ccnv F)) p0005
  have p0007 :=
    @g_funsi (syn_ccnv F)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_cnvsi F
  have p0010 :=
    @g_funeqi (syn_ccnv (syn_csi F)) (syn_csi (syn_ccnv F)) p0009
  have p0011 :=
    @g_mpbir (syn_wfun (syn_ccnv (syn_csi F))) (syn_wfun (syn_csi (syn_ccnv F))) p0008 p0010
  have p0012 :=
    @g_pm3_2i (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) (syn_wfun (syn_ccnv (syn_csi F))) p0003 p0011
  have p0013 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))))
  have p0014 :=
    @g_mpbir (syn_wf1 (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) (syn_wa (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) (syn_wfun (syn_ccnv (syn_csi F)))) p0012 p0013
  exact p0014

noncomputable def g_wppcardt2fnf1ndv
     :
    Nominal.NPrf (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_wppcardtfnf1ndv
  have p0001 :=
    @g_wppcardtfnf1ndv
  have p0002 :=
    @g_sif1mapndv (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn) p0001
  have p0003 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) (syn_wf1 (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs))) p0000 p0002
  have p0004 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    (by simpa [syn_cwppcardt2fn] using (Nominal.classEqRefl (syn_cwppcardt2fn)))
  have p0007 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbir (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf1 (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) p0005 p0008
  exact p0009

noncomputable def g_wppcardt4fnf1ndv
     :
    Nominal.NPrf (syn_wf1 (syn_cwppcardt4fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_wppcardt2fnf1ndv
  have p0001 :=
    @g_wppcardt2fnf1ndv
  have p0002 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) p0001
  have p0003 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt2fn)) p0002
  have p0004 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0000 p0003
  have p0005 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    (by simpa [syn_cwppcardt4fn] using (Nominal.classEqRefl (syn_cwppcardt4fn)))
  have p0008 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_mpbir (syn_wf1 (syn_cwppcardt4fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)) (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)) p0006 p0009
  exact p0010

noncomputable def g_wppfamilyrep2fnexndv
     :
    Nominal.NPrf (.classMem (syn_cwppfamilyrep2fn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwppfamilyrep2fn] using (Nominal.classEqRefl (syn_cwppfamilyrep2fn)))
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_fdpointrelex (syn_cvv) p0001
  have p0003 :=
    @g_imageex (syn_cfdpointrel (syn_cvv)) p0002
  have p0004 :=
    @g_eqeltri (syn_cwppfamilyrep2fn) (syn_cimage (syn_cfdpointrel (syn_cvv))) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_wppfamilyrep2fnfnndv
     :
    Nominal.NPrf (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_vvex
  have p0001 :=
    @g_fdpointrelex (syn_cvv) p0000
  have p0002 :=
    @g_wppimagefn (syn_cfdpointrel (syn_cvv)) p0001
  have p0003 :=
    (by simpa [syn_cwppfamilyrep2fn] using (Nominal.classEqRefl (syn_cwppfamilyrep2fn)))
  have p0004 :=
    @g_fneq1i (syn_cvv) (syn_cwppfamilyrep2fn) (syn_cimage (syn_cfdpointrel (syn_cvv))) p0003
  have p0005 :=
    @g_mpbir (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (syn_wfn (syn_cimage (syn_cfdpointrel (syn_cvv))) (syn_cvv)) p0002 p0004
  exact p0005

noncomputable def g_wppfamilyrep2fnvalndv
    (Q : Class) (hyp_wppfamilyrep2fnvalndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn Q))) (syn_cpw1 (syn_cpw1 Q))) := by
  let proofSupport : Finset Var := Q.fv
  have p0000 :=
    (by simpa [syn_cwppfamilyrep2fn] using (Nominal.classEqRefl (syn_cwppfamilyrep2fn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn Q)) (syn_cwppfamilyrep2fn) (syn_cimage (syn_cfdpointrel (syn_cvv))) p0000
  have p0002 :=
    @g_vvex
  have p0003 :=
    @g_fdpointrelex (syn_cvv) p0002
  have p0004 :=
    @g_snex (syn_csn Q)
  have p0005 :=
    @g_fvimagecl (syn_csn (syn_csn Q)) (syn_cfdpointrel (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_fdpointimagevvdndv Q
  have p0007 :=
    Nominal.mp hyp_wppfamilyrep2fnvalndv_1 p0006
  have p0008 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cfdpointrel (syn_cvv))) (syn_csn (syn_csn Q))) (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn Q))) (syn_cpw1 (syn_cpw1 Q)) p0005 p0007
  have p0009 :=
    @g_eqtri (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn Q))) (syn_cfv (syn_cimage (syn_cfdpointrel (syn_cvv))) (syn_csn (syn_csn Q))) (syn_cpw1 (syn_cpw1 Q)) p0001 p0008
  exact p0009

noncomputable def g_wppdirecte2famfnexndv
     :
    Nominal.NPrf (.classMem (syn_cwppdirecte2famfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwppdirecte2famfn] using (Nominal.classEqRefl (syn_cwppdirecte2famfn)))
  have p0001 :=
    @g_wpppowset2fnexndv
  have p0002 :=
    @g_imageex (syn_cwpppowset2fn) p0001
  have p0003 :=
    @g_wppfamilyrep2fnexndv
  have p0004 :=
    @g_coex (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn) p0002 p0003
  have p0005 :=
    @g_eqeltri (syn_cwppdirecte2famfn) (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) (syn_cvv) p0000 p0004
  exact p0005

noncomputable def g_wppdirecte2famfnfnndv
     :
    Nominal.NPrf (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_wpppowset2fnexndv
  have p0001 :=
    @g_wppimagefn (syn_cwpppowset2fn) p0000
  have p0002 :=
    @g_wppfamilyrep2fnfnndv
  have p0003 :=
    @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpppowset2fn)) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    (by simpa [syn_cwppdirecte2famfn] using (Nominal.classEqRefl (syn_cwppdirecte2famfn)))
  have p0009 :=
    @g_fneq1i (syn_cvv) (syn_cwppdirecte2famfn) (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) p0008
  have p0010 :=
    @g_mpbir (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) (syn_cvv)) p0007 p0009
  exact p0010

noncomputable def g_wppdirecte2famfnvalndv
    (Q : Class) (hyp_wppdirecte2famfnvalndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn Q))) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))) := by
  let proofSupport : Finset Var := Q.fv
  have p0000 :=
    (by simpa [syn_cwppdirecte2famfn] using (Nominal.classEqRefl (syn_cwppdirecte2famfn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn Q)) (syn_cwppdirecte2famfn) (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) p0000
  have p0002 :=
    @g_wppfamilyrep2fnfnndv
  have p0003 :=
    @g_snex (syn_csn Q)
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (.classMem (syn_csn (syn_csn Q)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_csn Q)) (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_wppfamilyrep2fnvalndv Q hyp_wppdirecte2famfnvalndv_1
  have p0008 :=
    @g_fveq2i (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn Q))) (syn_cpw1 (syn_cpw1 Q)) (syn_cimage (syn_cwpppowset2fn)) p0007
  have p0009 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn Q))) (syn_cfv (syn_cimage (syn_cwpppowset2fn)) (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn Q)))) (syn_cfv (syn_cimage (syn_cwpppowset2fn)) (syn_cpw1 (syn_cpw1 Q))) p0006 p0008
  have p0010 :=
    @g_wpppowset2fnexndv
  have p0011 :=
    @g_pw1ex Q hyp_wppdirecte2famfnvalndv_1
  have p0012 :=
    @g_pw1ex (syn_cpw1 Q) p0011
  have p0013 :=
    @g_fvimagecl (syn_cpw1 (syn_cpw1 Q)) (syn_cwpppowset2fn) p0010 p0012
  have p0014 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn Q))) (syn_cfv (syn_cimage (syn_cwpppowset2fn)) (syn_cpw1 (syn_cpw1 Q))) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) p0009 p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn Q))) (syn_cfv (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn Q))) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) p0001 p0014
  exact p0015

noncomputable def g_wppdirecth1famfnexndv
     :
    Nominal.NPrf (.classMem (syn_cwppdirecth1famfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwppdirecth1famfn] using (Nominal.classEqRefl (syn_cwppdirecth1famfn)))
  have p0001 :=
    @g_wpplitphnordpointfnexndv
  have p0002 :=
    @g_imageex (syn_cwpplitphnordpointfn) p0001
  have p0003 :=
    @g_wppfamilyrep2fnexndv
  have p0004 :=
    @g_coex (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn) p0002 p0003
  have p0005 :=
    @g_wppdirecte2famfnexndv
  have p0006 :=
    @g_siex (syn_cwppdirecte2famfn) p0005
  have p0007 :=
    @g_siex (syn_csi (syn_cwppdirecte2famfn)) p0006
  have p0008 :=
    @g_coex (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn))) p0004 p0007
  have p0009 :=
    @g_eqeltri (syn_cwppdirecth1famfn) (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) (syn_cvv) p0000 p0008
  exact p0009

noncomputable def g_wppdirecth1famfnfnndv
     :
    Nominal.NPrf (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_wpplitphnordpointfnexndv
  have p0001 :=
    @g_wppimagefn (syn_cwpplitphnordpointfn) p0000
  have p0002 :=
    @g_wppfamilyrep2fnfnndv
  have p0003 :=
    @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_wppdirecte2famfnfnndv
  have p0009 :=
    @g_dffn2 (syn_cvv) (syn_cwppdirecte2famfn)
  have p0010 :=
    @g_mpbi (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv)) (syn_wf (syn_cwppdirecte2famfn) (syn_cvv) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_sifmap (syn_cvv) (syn_cvv) (syn_cwppdirecte2famfn)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwppdirecte2famfn))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0018 :=
    @g_mpbi (syn_wfn (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wf (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0016 p0017
  have p0019 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_cvv)) (syn_wf (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0007 p0018
  have p0020 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    (by simpa [syn_cwppdirecth1famfn] using (Nominal.classEqRefl (syn_cwppdirecth1famfn)))
  have p0023 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn) (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) p0022
  have p0024 :=
    @g_mpbir (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wfn (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0021 p0023
  exact p0024

noncomputable def g_wppdirecth1famfnvalndv
    (Q : Class) (hyp_wppdirecth1famfnvalndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn Q))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q))))) := by
  let proofSupport : Finset Var := Q.fv
  have p0000 :=
    (by simpa [syn_cwppdirecth1famfn] using (Nominal.classEqRefl (syn_cwppdirecth1famfn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn Q)) (syn_cwppdirecth1famfn) (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) p0000
  have p0002 :=
    @g_wppdirecte2famfnfnndv
  have p0003 :=
    @g_dffn2 (syn_cvv) (syn_cwppdirecte2famfn)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv)) (syn_wf (syn_cwppdirecte2famfn) (syn_cvv) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_sifmap (syn_cvv) (syn_cvv) (syn_cwppdirecte2famfn)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_sifmap (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwppdirecte2famfn))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_snelpw1 Q (syn_cvv)
  have p0012 :=
    @g_mpbir (.classMem (syn_csn Q) (syn_cpw1 (syn_cvv))) (.classMem Q (syn_cvv)) hyp_wppdirecth1famfnvalndv_1 p0011
  have p0013 :=
    @g_snelpw1 (syn_csn Q) (syn_cpw1 (syn_cvv))
  have p0014 :=
    @g_mpbir (.classMem (syn_csn (syn_csn Q)) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.classMem (syn_csn Q) (syn_cpw1 (syn_cvv))) p0012 p0013
  have p0015 :=
    @g_pm3_2i (syn_wfn (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.classMem (syn_csn (syn_csn Q)) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0010 p0014
  have p0016 :=
    @g_fvco2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csn (syn_csn Q)) (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_snelpw1 Q (syn_cvv)
  have p0019 :=
    @g_mpbir (.classMem (syn_csn Q) (syn_cpw1 (syn_cvv))) (.classMem Q (syn_cvv)) hyp_wppdirecth1famfnvalndv_1 p0018
  have p0020 :=
    @g_wppdirecte2famfnfnndv
  have p0021 :=
    @g_dffn2 (syn_cvv) (syn_cwppdirecte2famfn)
  have p0022 :=
    @g_mpbi (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv)) (syn_wf (syn_cwppdirecte2famfn) (syn_cvv) (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_sifmap (syn_cvv) (syn_cvv) (syn_cwppdirecte2famfn)
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_sifvald (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csn Q) (syn_csi (syn_cwppdirecte2famfn)) p0024
  have p0026 :=
    Nominal.mp p0019 p0025
  have p0027 :=
    @g_wppdirecte2famfnfnndv
  have p0028 :=
    @g_dffn2 (syn_cvv) (syn_cwppdirecte2famfn)
  have p0029 :=
    @g_mpbi (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv)) (syn_wf (syn_cwppdirecte2famfn) (syn_cvv) (syn_cvv)) p0027 p0028
  have p0030 :=
    @g_sifvald (syn_cvv) (syn_cvv) Q (syn_cwppdirecte2famfn) p0029
  have p0031 :=
    Nominal.mp hyp_wppdirecth1famfnvalndv_1 p0030
  have p0032 :=
    @g_sneqi (syn_cfv (syn_csi (syn_cwppdirecte2famfn)) (syn_csn Q)) (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)) p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_csn (syn_csn Q))) (syn_csn (syn_cfv (syn_csi (syn_cwppdirecte2famfn)) (syn_csn Q))) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))) p0026 p0032
  have p0034 :=
    @g_fveq2i (syn_cfv (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_csn (syn_csn Q))) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))) (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) p0033
  have p0035 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) (syn_csn (syn_csn Q))) (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_cfv (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_csn (syn_csn Q)))) (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)))) p0017 p0034
  have p0036 :=
    @g_wppfamilyrep2fnfnndv
  have p0037 :=
    @g_snex (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))
  have p0038 :=
    @g_pm3_2i (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (.classMem (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))) (syn_cvv)) p0036 p0037
  have p0039 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))) (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_fvex Q (syn_cwppdirecte2famfn)
  have p0042 :=
    @g_wppfamilyrep2fnvalndv (syn_cfv (syn_cwppdirecte2famfn) Q) p0041
  have p0043 :=
    @g_fveq2i (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q))) (syn_cimage (syn_cwpplitphnordpointfn)) p0042
  have p0044 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)))) (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))))) (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q)))) p0040 p0043
  have p0045 :=
    @g_wpplitphnordpointfnexndv
  have p0046 :=
    @g_fvex Q (syn_cwppdirecte2famfn)
  have p0047 :=
    @g_pw1ex (syn_cfv (syn_cwppdirecte2famfn) Q) p0046
  have p0048 :=
    @g_pw1ex (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q)) p0047
  have p0049 :=
    @g_fvimagecl (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q))) (syn_cwpplitphnordpointfn) p0045 p0048
  have p0050 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)))) (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q)))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q)))) p0044 p0049
  have p0051 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) (syn_csn (syn_csn Q))) (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q)))) p0035 p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn Q))) (syn_cfv (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) (syn_csn (syn_csn Q))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q)))) p0001 p0051
  exact p0052

noncomputable def g_wppdirecth2famfnvalndv
    (Q : Class) (hyp_wppdirecth2famfnvalndv_1 : Nominal.NPrf (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cvv))))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppdirecth2famfn) (syn_csn (syn_csn Q))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q))))) := by
  let proofSupport : Finset Var := Q.fv
  have p0000 :=
    (by simpa [syn_cwppdirecth2famfn] using (Nominal.classEqRefl (syn_cwppdirecth2famfn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn Q)) (syn_cwppdirecth2famfn) (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) p0000
  have p0002 :=
    @g_wppdirecth1famfnfnndv
  have p0003 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwppdirecth1famfn))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_snelpw1 Q (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0012 :=
    @g_mpbir (.classMem (syn_csn Q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cvv)))) hyp_wppdirecth2famfnvalndv_1 p0011
  have p0013 :=
    @g_snelpw1 (syn_csn Q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0014 :=
    @g_mpbir (.classMem (syn_csn (syn_csn Q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (.classMem (syn_csn Q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0012 p0013
  have p0015 :=
    @g_pm3_2i (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (.classMem (syn_csn (syn_csn Q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0010 p0014
  have p0016 :=
    @g_fvco2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_csn (syn_csn Q)) (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_snelpw1 Q (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0019 :=
    @g_mpbir (.classMem (syn_csn Q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cvv)))) hyp_wppdirecth2famfnvalndv_1 p0018
  have p0020 :=
    @g_wppdirecth1famfnfnndv
  have p0021 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0022 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv)) (syn_csn Q) (syn_csi (syn_cwppdirecth1famfn)) p0024
  have p0026 :=
    Nominal.mp p0019 p0025
  have p0027 :=
    @g_wppdirecth1famfnfnndv
  have p0028 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0029 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0027 p0028
  have p0030 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) Q (syn_cwppdirecth1famfn) p0029
  have p0031 :=
    Nominal.mp hyp_wppdirecth2famfnvalndv_1 p0030
  have p0032 :=
    @g_sneqi (syn_cfv (syn_csi (syn_cwppdirecth1famfn)) (syn_csn Q)) (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)) p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_csn (syn_csn Q))) (syn_csn (syn_cfv (syn_csi (syn_cwppdirecth1famfn)) (syn_csn Q))) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))) p0026 p0032
  have p0034 :=
    @g_fveq2i (syn_cfv (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_csn (syn_csn Q))) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))) (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) p0033
  have p0035 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_csn (syn_csn Q))) (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_cfv (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_csn (syn_csn Q)))) (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)))) p0017 p0034
  have p0036 :=
    @g_wppfamilyrep2fnfnndv
  have p0037 :=
    @g_snex (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))
  have p0038 :=
    @g_pm3_2i (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (.classMem (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))) (syn_cvv)) p0036 p0037
  have p0039 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))) (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_fvex Q (syn_cwppdirecth1famfn)
  have p0042 :=
    @g_wppfamilyrep2fnvalndv (syn_cfv (syn_cwppdirecth1famfn) Q) p0041
  have p0043 :=
    @g_fveq2i (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q))) (syn_cimage (syn_cwpplitphnordpointfn)) p0042
  have p0044 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)))) (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))))) (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q)))) p0040 p0043
  have p0045 :=
    @g_wpplitphnordpointfnexndv
  have p0046 :=
    @g_fvex Q (syn_cwppdirecth1famfn)
  have p0047 :=
    @g_pw1ex (syn_cfv (syn_cwppdirecth1famfn) Q) p0046
  have p0048 :=
    @g_pw1ex (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q)) p0047
  have p0049 :=
    @g_fvimagecl (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q))) (syn_cwpplitphnordpointfn) p0045 p0048
  have p0050 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)))) (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q)))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q)))) p0044 p0049
  have p0051 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_csn (syn_csn Q))) (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q)))) p0035 p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_cwppdirecth2famfn) (syn_csn (syn_csn Q))) (syn_cfv (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_csn (syn_csn Q))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q)))) p0001 p0051
  exact p0052

noncomputable def g_wppconcrete6codefnvalndv
    (X : Class) (hyp_wppconcrete6codefnvalndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppconcrete6codefn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw X))))) := by
  let proofSupport : Finset Var := X.fv
  have p0000 :=
    (by simpa [syn_cwppconcrete6codefn] using (Nominal.classEqRefl (syn_cwppconcrete6codefn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))) (syn_cwppconcrete6codefn) (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) p0000
  have p0002 :=
    @g_wpplitphnordpointfnexndv
  have p0003 :=
    @g_wppimagefn (syn_cwpplitphnordpointfn) p0002
  have p0004 :=
    @g_wppfamilyrep2fnfnndv
  have p0005 :=
    @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0006 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_wppdirecth1famfnfnndv
  have p0011 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0012 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwppdirecth1famfn))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0020 :=
    @g_mpbi (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_cvv)) (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0009 p0020
  have p0022 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    (by simpa [syn_cwppdirecth2famfn] using (Nominal.classEqRefl (syn_cwppdirecth2famfn)))
  have p0025 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn) (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) p0024
  have p0026 :=
    @g_mpbir (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0023 p0025
  have p0027 :=
    @g_snex (syn_csn (syn_cnc X))
  have p0028 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_cnc X))) (syn_cvv)
  have p0029 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (syn_csn (syn_cnc X)))) (syn_cpw1 (syn_cvv))) (.classMem (syn_csn (syn_csn (syn_cnc X))) (syn_cvv)) p0027 p0028
  have p0030 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_cnc X)))) (syn_cpw1 (syn_cvv))
  have p0031 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.classMem (syn_csn (syn_csn (syn_csn (syn_cnc X)))) (syn_cpw1 (syn_cvv))) p0029 p0030
  have p0032 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))) (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0033 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0031 p0032
  have p0034 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0035 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0033 p0034
  have p0036 :=
    @g_pm3_2i (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0026 p0035
  have p0037 :=
    @g_fvco2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))) (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_snex (syn_csn (syn_cnc X))
  have p0040 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_cnc X))) (syn_cvv)
  have p0041 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (syn_csn (syn_cnc X)))) (syn_cpw1 (syn_cvv))) (.classMem (syn_csn (syn_csn (syn_cnc X))) (syn_cvv)) p0039 p0040
  have p0042 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_cnc X)))) (syn_cpw1 (syn_cvv))
  have p0043 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.classMem (syn_csn (syn_csn (syn_csn (syn_cnc X)))) (syn_cpw1 (syn_cvv))) p0041 p0042
  have p0044 :=
    @g_wppdirecth2famfnvalndv (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))) p0043
  have p0045 :=
    @g_fveq2i (syn_cfv (syn_cwppdirecth2famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))) (syn_cimage (syn_cen)) p0044
  have p0046 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))) (syn_cfv (syn_cimage (syn_cen)) (syn_cfv (syn_cwppdirecth2famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))) (syn_cfv (syn_cimage (syn_cen)) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))))) p0038 p0045
  have p0047 :=
    @g_snex (syn_csn (syn_cnc X))
  have p0048 :=
    @g_wppdirecth1famfnvalndv (syn_csn (syn_csn (syn_cnc X))) p0047
  have p0049 :=
    @g_ncex X
  have p0050 :=
    @g_wppdirecte2famfnvalndv (syn_cnc X) p0049
  have p0051 :=
    @g_ncex X
  have p0052 :=
    @g_wpppowset2imexndv (syn_cnc X) p0051
  have p0053 :=
    @g_eqeltri (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X)))) (syn_cvv) p0050 p0052
  have p0054 :=
    @g_wpplitphnordimexndv (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) p0053
  have p0055 :=
    @g_eqeltri (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X))))))) (syn_cvv) p0048 p0054
  have p0056 :=
    @g_ncex X
  have p0057 :=
    @g_wppdirecte2famfnvalndv (syn_cnc X) p0056
  have p0058 :=
    @g_ncex X
  have p0059 :=
    @g_wpppowset2imexndv (syn_cnc X) p0058
  have p0060 :=
    @g_eqeltri (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X)))) (syn_cvv) p0057 p0059
  have p0061 :=
    @g_ncex X
  have p0062 :=
    @g_enrflx X hyp_wppconcrete6codefnvalndv_1
  have p0063 :=
    @g_elnc X X
  have p0064 :=
    @g_mpbir (.classMem X (syn_cnc X)) (syn_wbr X (syn_cen) X) p0062 p0063
  have p0065 :=
    @g_wpppowset2imcanndv X (syn_cnc X) p0061 p0064
  have p0066 :=
    @g_ncex X
  have p0067 :=
    @g_wppdirecte2famfnvalndv (syn_cnc X) p0066
  have p0068 :=
    @g_eleq2i (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X)))) (syn_cpw (syn_cpw X)) p0067
  have p0069 :=
    @g_mpbir (.classMem (syn_cpw (syn_cpw X)) (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X))))) (.classMem (syn_cpw (syn_cpw X)) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X))))) p0065 p0068
  have p0070 :=
    @g_wpplitphnordimcanndv (syn_cpw (syn_cpw X)) (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) p0060 p0069
  have p0071 :=
    @g_snex (syn_csn (syn_cnc X))
  have p0072 :=
    @g_wppdirecth1famfnvalndv (syn_csn (syn_csn (syn_cnc X))) p0071
  have p0073 :=
    @g_eleq2i (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X))))))) (syn_chnord (syn_cpw (syn_cpw X))) p0072
  have p0074 :=
    @g_mpbir (.classMem (syn_chnord (syn_cpw (syn_cpw X))) (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))) (.classMem (syn_chnord (syn_cpw (syn_cpw X))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))))))) p0070 p0073
  have p0075 :=
    @g_snex (syn_csn (syn_cnc X))
  have p0076 :=
    @g_wppdirecth1famfnvalndv (syn_csn (syn_csn (syn_cnc X))) p0075
  have p0077 :=
    @g_ncex X
  have p0078 :=
    @g_wppdirecte2famfnvalndv (syn_cnc X) p0077
  have p0079 :=
    @g_ncex X
  have p0080 :=
    @g_wpppowset2imexndv (syn_cnc X) p0079
  have p0081 :=
    @g_eqeltri (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X)))) (syn_cvv) p0078 p0080
  have p0082 :=
    @g_ncex X
  have p0083 :=
    @g_wppdirecte2famfnvalndv (syn_cnc X) p0082
  have p0084 :=
    @g_ncex X
  have p0085 :=
    @g_ssid (syn_cnc X)
  have p0086 :=
    @g_wpppowset2imssndv X (syn_cnc X) p0084 p0085
  have p0087 :=
    @g_eqsstri (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X)))) (syn_cnc (syn_cpw (syn_cpw X))) p0083 p0086
  have p0088 :=
    @g_wpplitphnordimssndv (syn_cpw (syn_cpw X)) (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) p0081 p0087
  have p0089 :=
    @g_eqsstri (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X))))))) (syn_cnc (syn_chnord (syn_cpw (syn_cpw X)))) p0076 p0088
  have p0090 :=
    @g_wpplitphnordcardvalndv (syn_chnord (syn_cpw (syn_cpw X))) (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))) p0055 p0074 p0089
  have p0091 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))) (syn_cfv (syn_cimage (syn_cen)) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) p0046 p0090
  have p0092 :=
    @g_eqtri (syn_cfv (syn_cwppconcrete6codefn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))) (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) p0001 p0091
  exact p0092

noncomputable def g_wppcardt6fnmapndv
     :
    Nominal.NPrf (syn_wf (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_wppcardt2fnmapndv
  have p0001 :=
    @g_wppcardt4fnmapndv
  have p0002 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn))
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0000 p0005
  have p0007 :=
    @g_fco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    (by simpa [syn_cwppcardt6fn] using (Nominal.classEqRefl (syn_cwppcardt6fn)))
  have p0010 :=
    @g_feq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) p0009
  have p0011 :=
    @g_mpbir (syn_wf (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) (syn_wf (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) p0008 p0010
  exact p0011

#print axioms g_wppcardt6fnmapndv

end NFChoice.DirectNominalPrf.WPPReplay
