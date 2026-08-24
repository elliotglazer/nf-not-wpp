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
import NominalWPPReplayChunk016Compact001Part047

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

noncomputable def g_wpphitnestndv
    (m : Var) (n : Var) (F : Class) (H : Class) (I : Class) (L : Class) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_H_m : m ∉ H.fv) (dv_H_n : n ∉ H.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (dv_L_m : m ∉ L.fv) (dv_L_n : n ∉ L.fv) (dv_m_n : m ≠ n) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L))))) := by
  let proofSupport : Finset Var := ({m} : Finset Var) ∪ ({n} : Finset Var) ∪ F.fv ∪ H.fv ∪ I.fv ∪ L.fv
  have dv_cache_0001 : m ∉ ((Class.cv n)).fv := by
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_m_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : m ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : m ∉ ((Wff.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_m_n, dv_F_m, dv_I_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (F).fv ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (F).fv ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((F).fv) (({n} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show n ∉ (F).fv from (by exact dv_F_n))))))
  have dv_cache_0005 : Disjoint (I).fv ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (I).fv ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((I).fv) (({n} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show n ∉ (I).fv from (by exact dv_I_n))))))
  have dv_cache_0006 : n ∉ ((syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, dv_I_n, dv_L_n, dv_H_n, (Ne.symm dv_m_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))
  have p0001 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) p0000 p0001
  have p0003 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) p0002 p0003
  have p0005 :=
    @g_simpr (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))
  have p0006 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc)) p0004 p0005
  have p0007 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))
  have p0008 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) p0007 p0008
  have p0010 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)) p0009 p0010
  have p0012 :=
    @g_simp1 (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)) (.classMem L (syn_cncs)) p0011 p0012
  have p0014 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))
  have p0015 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) p0014 p0015
  have p0017 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)) p0016 p0017
  have p0019 :=
    @g_simp2 (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)) (.classMem H (syn_cncs)) p0018 p0019
  have p0021 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))
  have p0022 :=
    @g_simpr (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))) p0021 p0022
  have p0024 :=
    @g_simpr (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))
  have p0025 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) p0023 p0024
  have p0026 :=
    @g_fveq2 (.cv m) (.cv n) (syn_cfrec F I)
  have p0027 :=
    @g_eleq1d (.classEq (.cv m) (.cv n)) (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs) p0026
  have p0028 :=
    @g_rspccva (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs)) m (.cv n) (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0027
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs)) p0025 p0028
  have p0030 :=
    @g_n_3jca (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs)) p0013 p0020 p0029
  have p0031 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))
  have p0032 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) p0031 p0032
  have p0034 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)) p0033 p0034
  have p0036 :=
    @g_simp3 (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)) (syn_wbr L (syn_clec) H) p0035 p0036
  have p0038 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs))) (syn_wbr L (syn_clec) H) p0030 p0037
  have p0039 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs))) (syn_wbr L (syn_clec) H)) p0006 p0038
  have p0040 :=
    @g_wpphitnestptndv F H I L (.cv n) dv_cache_0004 dv_cache_0005
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs))) (syn_wbr L (syn_clec) H))) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L))) p0039 p0040
  have p0042 :=
    @g_ralrimiva (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L))) n (syn_cnnc) dv_cache_0006 p0041
  exact p0042

noncomputable def g_wpphitstepptndv
    (F : Class) (H : Class) (I : Class) (L : Class) (N : Class) (dv_F_N : Disjoint F.fv N.fv) (dv_I_N : Disjoint I.fv N.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (.imp (.classMem N (syn_cwpphit F I L)) (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I H)))) := by
  let proofSupport : Finset Var := F.fv ∪ H.fv ∪ I.fv ∪ L.fv ∪ N.fv
  have p0000 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
  have p0001 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) p0000 p0001
  have p0003 :=
    @g_elwpphitvndv L F I N
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wb (.classMem N (syn_cwpphit F I L)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)))) p0002 p0003
  have p0005 :=
    @g_biimpd (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (.classMem N (syn_cwpphit F I L)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))) p0004
  have p0006 :=
    @g_simpr (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
  have p0007 :=
    @g_syl6 (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (.classMem N (syn_cwpphit F I L)) (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0005 p0006
  have p0008 :=
    @g_simpr (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
  have p0009 :=
    @g_syld (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (.classMem N (syn_cwpphit F I L)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) p0007 p0008
  have p0010 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
  have p0011 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) p0010 p0011
  have p0013 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
  have p0014 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0015 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.classMem N (syn_cnnc)) p0013 p0014
  have p0016 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)) p0012 p0015
  have p0017 :=
    @g_elwpphitsucvndv H F I N
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wb (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I H)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))) p0016 p0017
  have p0019 :=
    @g_biimprd (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I H)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) p0018
  have p0020 :=
    @g_syld (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) (.classMem N (syn_cwpphit F I L)) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I H)) p0009 p0019
  exact p0020

noncomputable def g_wpphitstepndv
    (m : Var) (n : Var) (F : Class) (H : Class) (I : Class) (L : Class) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_H_m : m ∉ H.fv) (dv_H_n : n ∉ H.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (dv_L_m : m ∉ L.fv) (dv_L_n : n ∉ L.fv) (dv_m_n : m ≠ n) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H))))) := by
  let proofSupport : Finset Var := ({m} : Finset Var) ∪ ({n} : Finset Var) ∪ F.fv ∪ H.fv ∪ I.fv ∪ L.fv
  have dv_cache_0001 : m ∉ ((Class.cv n)).fv := by
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_m_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : m ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : m ∉ ((Wff.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_m, dv_m_n, dv_F_m, dv_I_m, dv_H_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (F).fv ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (F).fv ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((F).fv) (({n} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show n ∉ (F).fv from (by exact dv_F_n))))))
  have dv_cache_0005 : Disjoint (I).fv ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (I).fv ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((I).fv) (({n} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show n ∉ (I).fv from (by exact dv_I_n))))))
  have dv_cache_0006 : n ∉ ((syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, dv_I_n, dv_L_n, (Ne.symm dv_m_n), dv_H_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))
  have p0001 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) p0000 p0001
  have p0003 :=
    @g_simpr (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))
  have p0004 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc)) p0002 p0003
  have p0005 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))
  have p0006 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))) p0005 p0006
  have p0008 :=
    @g_simpr (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))
  have p0009 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))) (.classMem (.cv n) (syn_cnnc)) p0007 p0008
  have p0010 :=
    @g_fveq2 (.cv m) (.cv n) (syn_cfrec F I)
  have p0011 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cfv (syn_cfrec F I) (.cv n)) L (syn_clec) p0010
  have p0012 :=
    @g_fveq2 (.cv m) (.cv n) (syn_cfrec F I)
  have p0013 :=
    @g_fveq2d (.classEq (.cv m) (.cv n)) (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cfv (syn_cfrec F I) (.cv n)) F p0012
  have p0014 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n))) H (syn_clec) p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv m) (.cv n)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n)))) p0011 p0014
  have p0016 :=
    @g_rspccva (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n))))) m (.cv n) (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))) (.classMem (.cv n) (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n))))) p0009 p0016
  have p0018 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n))))) p0004 p0017
  have p0019 :=
    @g_wpphitstepptndv F H I L (.cv n) dv_cache_0004 dv_cache_0005
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n)))))) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H))) p0018 p0019
  have p0021 :=
    @g_ralrimiva (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H))) n (syn_cnnc) dv_cache_0006 p0020
  exact p0021

#print axioms g_wpphitstepndv

end NFChoice.DirectNominalPrf.WPPReplay
