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
import NominalWPPReplayChunk014Compact001Part003

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

noncomputable def g_fnfreclem2
    (ph : Wff) (F : Class) (G : Class) (I : Class) (V : Class) (X : Class) (hyp_fnfreclem2_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) (hyp_fnfreclem2_2 : Nominal.NPrf (.imp ph (.classMem G V))) (hyp_fnfreclem2_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G)))) (hyp_fnfreclem2_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wbr (syn_c0c) F X) (.classEq X I))) := by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv ∪ V.fv ∪ X.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_I : z ∉ I.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_w_not_F : w ∉ F.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_G : w ∉ G.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_I : w ∉ I.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_X : w ∉ X.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : w ∉ (G).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (I).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (syn_c0c) X)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : w ∉ ((syn_cproj1 (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((syn_cplc (syn_cproj1 (.cv z)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_c0c) F X)))
  have p0001 :=
    @g_snex (syn_cop (syn_c0c) I)
  have p0002 :=
    @g_csucex w
  have p0003 :=
    @g_pprodexg (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G (syn_cvv) V
  have p0004 :=
    @g_sylancr ph (.classMem (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv)) (.classMem G V) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) p0002 hyp_fnfreclem2_2 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec w G I dv_cache_0001 dv_cache_0002
  have p0006 :=
    @g_eqtri F (syn_cfrec G I) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)) hyp_fnfreclem2_1 p0005
  have p0007 :=
    @g_clos1basesucg z (syn_cop (syn_c0c) X) F (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0006
  have p0008 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv)) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) (syn_wb (.classMem (syn_cop (syn_c0c) X) F) (syn_wo (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex z F (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X))))) p0001 p0004 p0007
  have p0009 :=
    @g_n_0cex
  have p0010 :=
    @g_opexg (syn_c0c) I (syn_cvv) (syn_cdm G)
  have p0011 :=
    @g_sylancr ph (.classMem (syn_c0c) (syn_cvv)) (.classMem I (syn_cdm G)) (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) p0009 hyp_fnfreclem2_3 p0010
  have p0012 :=
    @g_elsnc2g (syn_cop (syn_c0c) X) (syn_cop (syn_c0c) I) (syn_cvv)
  have p0013 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) (syn_wb (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I))) (.classEq (syn_cop (syn_c0c) X) (syn_cop (syn_c0c) I))) p0011 p0012
  have p0014 :=
    @g_opth (syn_c0c) X (syn_c0c) I
  have p0015 :=
    @g_simprbi (.classEq (syn_cop (syn_c0c) X) (syn_cop (syn_c0c) I)) (.classEq (syn_c0c) (syn_c0c)) (.classEq X I) p0014
  have p0016 :=
    @g_syl6bi ph (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I))) (.classEq (syn_cop (syn_c0c) X) (syn_cop (syn_c0c) I)) (.classEq X I) p0013 p0015
  have p0017 :=
    @g_n_0cnsuc (syn_cproj1 (.cv z))
  have p0018 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c))))
  have p0019 :=
    @g_mpbi (syn_wne (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c)) (.neg (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c))) p0017 p0018
  have p0020 :=
    @g_intnanr (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c)) (syn_wbr (syn_cproj2 (.cv z)) G X) p0019
  have p0021 :=
    @g_qrpprod (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z)) (syn_c0c) X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0022 :=
    @g_opeq (.cv z)
  have p0023 :=
    @g_breq1i (.cv z) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) (syn_cop (syn_c0c) X) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) p0022
  have p0024 :=
    @g_vex z
  have p0025 :=
    @g_proj1ex (.cv z) p0024
  have p0026 :=
    @g_addceq1 (.cv w) (syn_cproj1 (.cv z)) (syn_c1c)
  have p0027 :=
    @g_eqid (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
  have p0028 :=
    @g_n_1cex
  have p0029 :=
    @g_addcex (syn_cproj1 (.cv z)) (syn_c1c) p0025 p0028
  have p0030 :=
    @g_fvmpt w (syn_cproj1 (.cv z)) (syn_cplc (.cv w) (syn_c1c)) (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_cvv) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0026 p0027 p0029
  have p0031 :=
    Nominal.mp p0025 p0030
  have p0032 :=
    @g_eqeq1i (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cproj1 (.cv z))) (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c) p0031
  have p0033 :=
    @g_vex w
  have p0034 :=
    @g_n_1cex
  have p0035 :=
    @g_addcex (.cv w) (syn_c1c) p0033 p0034
  have p0036 :=
    @g_fnmpti w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) dv_cache_0009 p0035 p0027
  have p0037 :=
    @g_fnbrfvb (syn_cvv) (syn_cproj1 (.cv z)) (syn_c0c) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
  have p0038 :=
    @g_mp2an (syn_wfn (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv)) (.classMem (syn_cproj1 (.cv z)) (syn_cvv)) (syn_wb (.classEq (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cproj1 (.cv z))) (syn_c0c)) (syn_wbr (syn_cproj1 (.cv z)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_c0c))) p0036 p0025 p0037
  have p0039 :=
    @g_bitr3i (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c)) (.classEq (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cproj1 (.cv z))) (syn_c0c)) (syn_wbr (syn_cproj1 (.cv z)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_c0c)) p0032 p0038
  have p0040 :=
    @g_anbi1i (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c)) (syn_wbr (syn_cproj1 (.cv z)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_c0c)) (syn_wbr (syn_cproj2 (.cv z)) G X) p0039
  have p0041 :=
    @g_n_3bitr4i (syn_wbr (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X)) (syn_wa (syn_wbr (syn_cproj1 (.cv z)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_c0c)) (syn_wbr (syn_cproj2 (.cv z)) G X)) (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X)) (syn_wa (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c)) (syn_wbr (syn_cproj2 (.cv z)) G X)) p0021 p0023 p0040
  have p0042 :=
    @g_mtbir (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X)) (syn_wa (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c)) (syn_wbr (syn_cproj2 (.cv z)) G X)) p0020 p0041
  have p0043 :=
    @g_a1i (.neg (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X))) (.classMem (.cv z) F) p0042
  have p0044 :=
    @g_nrex (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X)) z F p0043
  have p0045 :=
    @g_pm2_21i (syn_wrex z F (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X))) (.classEq X I) p0044
  have p0046 :=
    @g_a1i (.imp (syn_wrex z F (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X))) (.classEq X I)) ph p0045
  have p0047 :=
    @g_jaod ph (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I))) (.classEq X I) (syn_wrex z F (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X))) p0016 p0046
  have p0048 :=
    @g_sylbid ph (.classMem (syn_cop (syn_c0c) X) F) (syn_wo (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex z F (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) X)))) (.classEq X I) p0008 p0047
  have p0049 :=
    @g_syl5bi (syn_wbr (syn_c0c) F X) (.classMem (syn_cop (syn_c0c) X) F) ph (.classEq X I) p0000 p0048
  exact p0049

noncomputable def g_fnfreclem3
    (ph : Wff) (z : Var) (F : Class) (G : Class) (I : Class) (V : Class) (X : Class) (Y : Class) (dv_F_z : z ∉ F.fv) (dv_G_z : z ∉ G.fv) (dv_I_z : z ∉ I.fv) (dv_X_z : z ∉ X.fv) (dv_Y_z : z ∉ Y.fv) (dv_ph_z : z ∉ ph.fv) (hyp_fnfreclem2_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) (hyp_fnfreclem2_2 : Nominal.NPrf (.imp ph (.classMem G V))) (hyp_fnfreclem2_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G)))) (hyp_fnfreclem2_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) (hyp_fnfreclem3_5 : Nominal.NPrf (.imp ph (.classMem X (syn_cnnc)))) (hyp_fnfreclem3_6 : Nominal.NPrf (.imp ph (syn_wbr (syn_cplc X (syn_c1c)) F Y))) :
    Nominal.NPrf (.imp ph (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({z} : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv ∪ V.fv ∪ X.fv ∪ Y.fv
  let a : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_ph : a ∉ ph.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_I : a ∉ I.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_V : a ∉ V.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_Y : a ∉ Y.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_w_not_F : w ∉ F.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_w_not_G : w ∉ G.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_I : w ∉ I.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_X : w ∉ X.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_Y : w ∉ Y.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_ph : t ∉ ph.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_t_not_F : t ∉ F.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_t_not_G : t ∉ G.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_t_not_I : t ∉ I.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t_not_V : t ∉ V.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_Y : t ∉ Y.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_a_ne_w : a ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_a : w ≠ a :=
    Ne.symm fresh_a_ne_w
  have fresh_a_ne_t : a ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_a : t ≠ a :=
    Ne.symm fresh_a_ne_t
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have dv_cache_0001 : t ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show t ≠ z from (by exact fresh_t_ne_z))
  have dv_cache_0004 : w ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_cplc (.cv t) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_X, fresh_t_ne_z, fresh_t_not_F, fresh_t_not_Y, fresh_t_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_ph, fresh_t_ne_a, fresh_t_not_F, fresh_t_not_X, fresh_t_not_Y, fresh_t_ne_w, fresh_t_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, fresh_z_ne_a, dv_F_z, dv_X_z, dv_Y_z, fresh_z_ne_w, dv_G_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_X, fresh_a_ne_z, fresh_a_not_F, fresh_a_not_Y, fresh_a_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ (I).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_cop (syn_cplc X (syn_c1c)) Y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_X, fresh_a_not_Y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ ((syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_w, fresh_a_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_0cex
  have p0001 :=
    @g_opexg (syn_c0c) I (syn_cvv) (syn_cdm G)
  have p0002 :=
    @g_sylancr ph (.classMem (syn_c0c) (syn_cvv)) (.classMem I (syn_cdm G)) (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) p0000 hyp_fnfreclem2_3 p0001
  have p0003 :=
    @g_elsnc2g (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I) (syn_cvv)
  have p0004 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) (syn_wb (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I))) (.classEq (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I))) p0002 p0003
  have p0005 :=
    @g_opth (syn_cplc X (syn_c1c)) Y (syn_c0c) I
  have p0006 :=
    @g_simplbi (.classEq (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I)) (.classEq (syn_cplc X (syn_c1c)) (syn_c0c)) (.classEq Y I) p0005
  have p0007 :=
    @g_n_0cnsuc X
  have p0008 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cplc X (syn_c1c)) (syn_c0c))))
  have p0009 :=
    @g_mpbi (syn_wne (syn_cplc X (syn_c1c)) (syn_c0c)) (.neg (.classEq (syn_cplc X (syn_c1c)) (syn_c0c))) p0007 p0008
  have p0010 :=
    @g_pm2_21i (.classEq (syn_cplc X (syn_c1c)) (syn_c0c)) (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0009
  have p0011 :=
    @g_a1i (.imp (.classEq (syn_cplc X (syn_c1c)) (syn_c0c)) (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)))) ph p0010
  have p0012 :=
    @g_syl5 (.classEq (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I)) (.classEq (syn_cplc X (syn_c1c)) (syn_c0c)) ph (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0006 p0011
  have p0013 :=
    @g_sylbid ph (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I))) (.classEq (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I)) (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0004 p0012
  have p0014 :=
    @g_vex a
  have p0015 :=
    @g_opeqex t z (.cv a) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_excom (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) t z
  have p0018 :=
    @g_mpbi (syn_wex t (syn_wex z (.classEq (.cv a) (syn_cop (.cv t) (.cv z))))) (syn_wex z (syn_wex t (.classEq (.cv a) (syn_cop (.cv t) (.cv z))))) p0016 p0017
  have p0019 :=
    @g_eleq1 (.cv a) (syn_cop (.cv t) (.cv z)) F
  have p0020 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv t) F (.cv z))))
  have p0021 :=
    @g_syl6bbr (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) (.classMem (.cv a) F) (.classMem (syn_cop (.cv t) (.cv z)) F) (syn_wbr (.cv t) F (.cv z)) p0019 p0020
  have p0022 :=
    @g_anbi2d (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) (.classMem (.cv a) F) (syn_wbr (.cv t) F (.cv z)) ph p0021
  have p0023 :=
    @g_breq1 (.cv a) (syn_cop (.cv t) (.cv z)) (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
  have p0024 :=
    @g_qrpprod (.cv t) (.cv z) (syn_cplc X (syn_c1c)) Y (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0025 :=
    @g_vex t
  have p0026 :=
    @g_addceq1 (.cv w) (.cv t) (syn_c1c)
  have p0027 :=
    @g_eqid (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
  have p0028 :=
    @g_n_1cex
  have p0029 :=
    @g_addcex (.cv t) (syn_c1c) p0025 p0028
  have p0030 :=
    @g_fvmpt w (.cv t) (syn_cplc (.cv w) (syn_c1c)) (syn_cplc (.cv t) (syn_c1c)) (syn_cvv) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0026 p0027 p0029
  have p0031 :=
    Nominal.mp p0025 p0030
  have p0032 :=
    @g_eqeq1i (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (.cv t)) (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c)) p0031
  have p0033 :=
    @g_fnmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv) dv_cache_0006 p0027
  have p0034 :=
    @g_n_1cex
  have p0035 :=
    @g_addcexg (.cv w) (syn_c1c) (syn_cvv) (syn_cvv)
  have p0036 :=
    @g_mpan2 (.classMem (.cv w) (syn_cvv)) (.classMem (syn_c1c) (syn_cvv)) (.classMem (syn_cplc (.cv w) (syn_c1c)) (syn_cvv)) p0034 p0035
  have p0037 :=
    @g_mprg (.classMem (syn_cplc (.cv w) (syn_c1c)) (syn_cvv)) (syn_wfn (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv)) w (syn_cvv) p0033 p0036
  have p0038 :=
    @g_fnbrfvb (syn_cvv) (.cv t) (syn_cplc X (syn_c1c)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
  have p0039 :=
    @g_mp2an (syn_wfn (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv)) (.classMem (.cv t) (syn_cvv)) (syn_wb (.classEq (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (.cv t)) (syn_cplc X (syn_c1c))) (syn_wbr (.cv t) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c)))) p0037 p0025 p0038
  have p0040 :=
    @g_bitr3i (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (.classEq (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (.cv t)) (syn_cplc X (syn_c1c))) (syn_wbr (.cv t) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c))) p0032 p0039
  have p0041 :=
    @g_anbi1i (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (syn_wbr (.cv t) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c))) (syn_wbr (.cv z) G Y) p0040
  have p0042 :=
    @g_bitr4i (syn_wbr (syn_cop (.cv t) (.cv z)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)) (syn_wa (syn_wbr (.cv t) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c))) (syn_wbr (.cv z) G Y)) (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (syn_wbr (.cv z) G Y)) p0024 p0041
  have p0043 :=
    @g_syl6bb (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)) (syn_wbr (syn_cop (.cv t) (.cv z)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)) (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (syn_wbr (.cv z) G Y)) p0023 p0042
  have p0044 :=
    @g_anbi12d (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) (syn_wa ph (.classMem (.cv a) F)) (syn_wa ph (syn_wbr (.cv t) F (.cv z))) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)) (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (syn_wbr (.cv z) G Y)) p0022 p0043
  have p0045 :=
    @g_breldm (.cv t) (.cv z) F
  have p0046 :=
    @g_adantl (syn_wbr (.cv t) F (.cv z)) (.classMem (.cv t) (syn_cdm F)) ph p0045
  have p0047 :=
    @g_dmfrec ph F G I V hyp_fnfreclem2_1 hyp_fnfreclem2_2 hyp_fnfreclem2_3 hyp_fnfreclem2_4
  have p0048 :=
    @g_adantr ph (.classEq (syn_cdm F) (syn_cnnc)) (syn_wbr (.cv t) F (.cv z)) p0047
  have p0049 :=
    @g_eleqtrd (syn_wa ph (syn_wbr (.cv t) F (.cv z))) (.cv t) (syn_cdm F) (syn_cnnc) p0046 p0048
  have p0050 :=
    @g_adantr ph (.classMem X (syn_cnnc)) (syn_wbr (.cv t) F (.cv z)) hyp_fnfreclem3_5
  have p0051 :=
    @g_peano4 (.cv t) X
  have p0052 :=
    @g_n_3expia (.classMem (.cv t) (syn_cnnc)) (.classMem X (syn_cnnc)) (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (.classEq (.cv t) X) p0051
  have p0053 :=
    @g_syl2anc (syn_wa ph (syn_wbr (.cv t) F (.cv z))) (.classMem (.cv t) (syn_cnnc)) (.classMem X (syn_cnnc)) (.imp (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (.classEq (.cv t) X)) p0049 p0050 p0052
  have p0054 :=
    @g_breq1 (.cv t) X (.cv z) F
  have p0055 :=
    @g_biimpcd (.classEq (.cv t) X) (syn_wbr (.cv t) F (.cv z)) (syn_wbr X F (.cv z)) p0054
  have p0056 :=
    @g_adantl (syn_wbr (.cv t) F (.cv z)) (.imp (.classEq (.cv t) X) (syn_wbr X F (.cv z))) ph p0055
  have p0057 :=
    @g_syld (syn_wa ph (syn_wbr (.cv t) F (.cv z))) (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (.classEq (.cv t) X) (syn_wbr X F (.cv z)) p0053 p0056
  have p0058 :=
    @g_anim1d (syn_wa ph (syn_wbr (.cv t) F (.cv z))) (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y) p0057
  have p0059 :=
    @g_imp (syn_wa ph (syn_wbr (.cv t) F (.cv z))) (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (syn_wbr (.cv z) G Y)) (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) p0058
  have p0060 :=
    @g_syl6bi (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y))) (syn_wa (syn_wa ph (syn_wbr (.cv t) F (.cv z))) (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (syn_wbr (.cv z) G Y))) (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) p0044 p0059
  have p0061 :=
    @g_com12 (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y))) (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) p0060
  have p0062 :=
    @g_exlimdv (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y))) (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) t dv_cache_0007 dv_cache_0008 p0061
  have p0063 :=
    @g_eximdv (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y))) (syn_wex t (.classEq (.cv a) (syn_cop (.cv t) (.cv z)))) (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) z dv_cache_0009 p0062
  have p0064 :=
    @g_mpi (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y))) (syn_wex z (syn_wex t (.classEq (.cv a) (syn_cop (.cv t) (.cv z))))) (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0018 p0063
  have p0065 :=
    @g_ex (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)) (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0064
  have p0066 :=
    @g_rexlimdva ph (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)) (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) a F dv_cache_0010 dv_cache_0011 p0065
  have p0067 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cplc X (syn_c1c)) F Y)))
  have p0068 :=
    @g_snex (syn_cop (syn_c0c) I)
  have p0069 :=
    @g_csucex w
  have p0070 :=
    @g_pprodexg (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G (syn_cvv) V
  have p0071 :=
    @g_sylancr ph (.classMem (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv)) (.classMem G V) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) p0069 hyp_fnfreclem2_2 p0070
  have p0072 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec w G I dv_cache_0012 dv_cache_0013
  have p0073 :=
    @g_eqtri F (syn_cfrec G I) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)) hyp_fnfreclem2_1 p0072
  have p0074 :=
    @g_clos1basesucg a (syn_cop (syn_cplc X (syn_c1c)) Y) F (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 p0073
  have p0075 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv)) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) (syn_wb (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) F) (syn_wo (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex a F (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y))))) p0068 p0071 p0074
  have p0076 :=
    @g_syl5bb (syn_wbr (syn_cplc X (syn_c1c)) F Y) (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) F) ph (syn_wo (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex a F (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)))) p0067 p0075
  have p0077 :=
    @g_mpbid ph (syn_wbr (syn_cplc X (syn_c1c)) F Y) (syn_wo (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex a F (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y)))) hyp_fnfreclem3_6 p0076
  have p0078 :=
    @g_mpjaod ph (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I))) (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) (syn_wrex a F (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc X (syn_c1c)) Y))) p0013 p0066 p0077
  exact p0078

#print axioms g_fnfreclem3

end NFChoice.DirectNominalPrf.WPPReplay
