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
import NominalWPPReplayChunk014Compact001Part002

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

noncomputable def g_frecxpg
    (F : Class) (G : Class) (I : Class) (V : Class) (hyp_frecxpg_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) :
    Nominal.NPrf (.imp (.classMem G V) (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ I.fv ∪ V.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_F : g ∉ F.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_g_not_G : g ∉ G.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_I : g ∉ I.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_V : g ∉ V.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have dv_cache_0001 : g ∉ (G).fv := by
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : g ∉ ((syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_G, fresh_g_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqid I
  have p0001 :=
    @g_freceq12 (.cv g) G I I
  have p0002 :=
    @g_mpan2 (.classEq (.cv g) G) (.classEq I I) (.classEq (syn_cfrec (.cv g) I) (syn_cfrec G I)) p0000 p0001
  have p0003 :=
    @g_rneq (.cv g) G
  have p0004 :=
    @g_uneq1d (.classEq (.cv g) G) (syn_crn (.cv g)) (syn_crn G) (syn_csn I) p0003
  have p0005 :=
    @g_xpeq2d (.classEq (.cv g) G) (syn_cun (syn_crn (.cv g)) (syn_csn I)) (syn_cun (syn_crn G) (syn_csn I)) (syn_cnnc) p0004
  have p0006 :=
    @g_sseq12d (.classEq (.cv g) G) (syn_cfrec (.cv g) I) (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn (.cv g)) (syn_csn I))) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) p0002 p0005
  have p0007 :=
    @g_eqid (syn_cfrec (.cv g) I)
  have p0008 :=
    @g_vex g
  have p0009 :=
    @g_frecxp (syn_cfrec (.cv g) I) (.cv g) I p0007 p0008
  have p0010 :=
    @g_vtoclg (syn_wss (syn_cfrec (.cv g) I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn (.cv g)) (syn_csn I)))) (syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) g G V dv_cache_0001 dv_cache_0002 p0006 p0009
  have p0011 :=
    @g_syl5eqss (.classMem G V) F (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) hyp_frecxpg_1 p0010
  exact p0011

noncomputable def g_dmfrec
    (ph : Wff) (F : Class) (G : Class) (I : Class) (V : Class) (hyp_dmfrec_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) (hyp_dmfrec_2 : Nominal.NPrf (.imp ph (.classMem G V))) (hyp_dmfrec_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G)))) (hyp_dmfrec_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cdm F) (syn_cnnc))) := by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let z : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_ph : t ∉ ph.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_t_not_F : t ∉ F.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t_not_G : t ∉ G.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_I : t ∉ I.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_V : t ∉ V.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_w_not_F : w ∉ F.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_G : w ∉ G.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_I : w ∉ I.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_I : y ∉ I.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_I : z ∉ I.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_t_ne_w : t ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_t : w ≠ t :=
    Ne.symm fresh_t_ne_w
  have fresh_t_ne_y : t ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_w_ne_y : w ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
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
  have dv_cache_0003 : t ∉ ((syn_cop (syn_c0c) I)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_w, fresh_t_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((Wff.classMem (.cv y) (syn_cdm G))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((syn_cplc (.cv x) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classMem (syn_cop (.cv x) (.cv y)) F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cplc (.cv x) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((Wff.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((syn_cdm F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_frecxpg F G I V hyp_dmfrec_1
  have p0001 :=
    @g_dmss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))
  have p0002 :=
    @g_n_3syl ph (.classMem G V) (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) (syn_wss (syn_cdm F) (syn_cdm (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))) hyp_dmfrec_2 p0000 p0001
  have p0003 :=
    @g_dmxpss (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))
  have p0004 :=
    @g_syl6ss ph (syn_cdm F) (syn_cdm (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) (syn_cnnc) p0002 p0003
  have p0005 :=
    @g_frecexg F G I V hyp_dmfrec_1
  have p0006 :=
    @g_syl ph (.classMem G V) (.classMem F (syn_cvv)) hyp_dmfrec_2 p0005
  have p0007 :=
    @g_dmexg F (syn_cvv)
  have p0008 :=
    @g_syl ph (.classMem F (syn_cvv)) (.classMem (syn_cdm F) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_n_0cex
  have p0010 :=
    @g_opexg (syn_c0c) I (syn_cvv) (syn_cdm G)
  have p0011 :=
    @g_mpan (.classMem (syn_c0c) (syn_cvv)) (.classMem I (syn_cdm G)) (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_syl ph (.classMem I (syn_cdm G)) (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) hyp_dmfrec_3 p0011
  have p0013 :=
    @g_snidg (syn_cop (syn_c0c) I) (syn_cvv)
  have p0014 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) p0012 p0013
  have p0015 :=
    @g_orcd ph (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex t F (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) I))) p0014
  have p0016 :=
    @g_snex (syn_cop (syn_c0c) I)
  have p0017 :=
    @g_csucex w
  have p0018 :=
    @g_pprodexg (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G (syn_cvv) V
  have p0019 :=
    @g_mpan (.classMem (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv)) (.classMem G V) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) p0017 p0018
  have p0020 :=
    @g_syl ph (.classMem G V) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) hyp_dmfrec_2 p0019
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec w G I dv_cache_0001 dv_cache_0002
  have p0022 :=
    @g_eqtri F (syn_cfrec G I) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)) hyp_dmfrec_1 p0021
  have p0023 :=
    @g_clos1basesucg t (syn_cop (syn_c0c) I) F (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0022
  have p0024 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv)) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) (syn_wb (.classMem (syn_cop (syn_c0c) I) F) (syn_wo (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex t F (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) I))))) p0016 p0020 p0023
  have p0025 :=
    @g_mpbird ph (.classMem (syn_cop (syn_c0c) I) F) (syn_wo (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex t F (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_c0c) I)))) p0015 p0024
  have p0026 :=
    @g_opeldm (syn_c0c) I F
  have p0027 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) F) (.classMem (syn_c0c) (syn_cdm F)) p0025 p0026
  have p0028 :=
    @g_eldm2 y (.cv x) F dv_cache_0007 dv_cache_0008
  have p0029 :=
    @g_clos1basesucg t (syn_cop (.cv x) (.cv y)) F (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0009 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0022
  have p0030 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv)) (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv)) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wo (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex t F (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y)))))) p0016 p0020 p0029
  have p0031 :=
    @g_vex x
  have p0032 :=
    @g_vex y
  have p0033 :=
    @g_opex (.cv x) (.cv y) p0031 p0032
  have p0034 :=
    @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop (syn_c0c) I) p0033
  have p0035 :=
    @g_opth (.cv x) (.cv y) (syn_c0c) I
  have p0036 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop (syn_c0c) I)) (syn_wa (.classEq (.cv x) (syn_c0c)) (.classEq (.cv y) I)) p0034 p0035
  have p0037 :=
    @g_simprbi (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I))) (.classEq (.cv x) (syn_c0c)) (.classEq (.cv y) I) p0036
  have p0038 :=
    @g_eleq1 (.cv y) I (syn_cdm G)
  have p0039 :=
    @g_biimprcd (.classEq (.cv y) I) (.classMem (.cv y) (syn_cdm G)) (.classMem I (syn_cdm G)) p0038
  have p0040 :=
    @g_syl ph (.classMem I (syn_cdm G)) (.imp (.classEq (.cv y) I) (.classMem (.cv y) (syn_cdm G))) hyp_dmfrec_3 p0039
  have p0041 :=
    @g_syl5 (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I))) (.classEq (.cv y) I) ph (.classMem (.cv y) (syn_cdm G)) p0037 p0040
  have p0042 :=
    @g_opeq (.cv t)
  have p0043 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) p0042
  have p0044 :=
    @g_qrpprod (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (.cv x) (.cv y) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0045 :=
    @g_bitri (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y))) (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (syn_cproj1 (.cv t)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (.cv x)) (syn_wbr (syn_cproj2 (.cv t)) G (.cv y))) p0043 p0044
  have p0046 :=
    @g_simprbi (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y))) (syn_wbr (syn_cproj1 (.cv t)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (.cv x)) (syn_wbr (syn_cproj2 (.cv t)) G (.cv y)) p0045
  have p0047 :=
    @g_brelrn (syn_cproj2 (.cv t)) (.cv y) G
  have p0048 :=
    @g_syl (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y))) (syn_wbr (syn_cproj2 (.cv t)) G (.cv y)) (.classMem (.cv y) (syn_crn G)) p0046 p0047
  have p0049 :=
    @g_sseld ph (syn_crn G) (syn_cdm G) (.cv y) hyp_dmfrec_4
  have p0050 :=
    @g_syl5 (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y))) (.classMem (.cv y) (syn_crn G)) ph (.classMem (.cv y) (syn_cdm G)) p0048 p0049
  have p0051 :=
    @g_adantr ph (.imp (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y))) (.classMem (.cv y) (syn_cdm G))) (.classMem (.cv t) F) p0050
  have p0052 :=
    @g_rexlimdva ph (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y))) (.classMem (.cv y) (syn_cdm G)) t F dv_cache_0010 dv_cache_0011 p0051
  have p0053 :=
    @g_jaod ph (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I))) (.classMem (.cv y) (syn_cdm G)) (syn_wrex t F (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y)))) p0041 p0052
  have p0054 :=
    @g_sylbid ph (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wo (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex t F (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (.cv x) (.cv y))))) (.classMem (.cv y) (syn_cdm G)) p0030 p0053
  have p0055 :=
    @g_ancld ph (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv y) (syn_cdm G)) p0054
  have p0056 :=
    @g_clos1conn (syn_cop (.cv x) (.cv y)) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)) F (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_csn (syn_cop (syn_c0c) I)) p0022
  have p0057 :=
    @g_eximi (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)))) (.classMem (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)) F) z p0056
  have p0058 :=
    @g_eldm z (.cv y) G dv_cache_0012 dv_cache_0013
  have p0059 :=
    @g_eqid (syn_cplc (.cv x) (syn_c1c))
  have p0060 :=
    @g_n_1cex
  have p0061 :=
    @g_addcex (.cv x) (syn_c1c) p0031 p0060
  have p0062 :=
    @g_brcsuc w (.cv x) (syn_cplc (.cv x) (syn_c1c)) dv_cache_0014 dv_cache_0015 p0031 p0061
  have p0063 :=
    @g_mpbir (syn_wbr (.cv x) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc (.cv x) (syn_c1c))) (.classEq (syn_cplc (.cv x) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c))) p0059 p0062
  have p0064 :=
    @g_qrpprod (.cv x) (.cv y) (syn_cplc (.cv x) (syn_c1c)) (.cv z) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0065 :=
    @g_mpbiran (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))) (syn_wbr (.cv x) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc (.cv x) (syn_c1c))) (syn_wbr (.cv y) G (.cv z)) p0063 p0064
  have p0066 :=
    @g_exbii (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))) (syn_wbr (.cv y) G (.cv z)) z p0065
  have p0067 :=
    @g_bitr4i (.classMem (.cv y) (syn_cdm G)) (syn_wex z (syn_wbr (.cv y) G (.cv z))) (syn_wex z (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)))) p0058 p0066
  have p0068 :=
    @g_anbi2i (.classMem (.cv y) (syn_cdm G)) (syn_wex z (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)))) (.classMem (syn_cop (.cv x) (.cv y)) F) p0067
  have p0069 :=
    @g_n_19_42v (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))) z dv_cache_0016
  have p0070 :=
    @g_bitr4i (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv y) (syn_cdm G))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wex z (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))))) (syn_wex z (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))))) p0068 p0069
  have p0071 :=
    @g_eldm2 z (syn_cplc (.cv x) (syn_c1c)) F dv_cache_0017 dv_cache_0018
  have p0072 :=
    @g_n_3imtr4i (syn_wex z (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))))) (syn_wex z (.classMem (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv y) (syn_cdm G))) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)) p0057 p0070 p0071
  have p0073 :=
    @g_syl6 ph (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv y) (syn_cdm G))) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)) p0055 p0072
  have p0074 :=
    @g_exlimdv ph (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)) y dv_cache_0019 dv_cache_0020 p0073
  have p0075 :=
    @g_syl5bi (.classMem (.cv x) (syn_cdm F)) (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) F)) ph (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)) p0028 p0074
  have p0076 :=
    @g_ralrimivw ph (.imp (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F))) x (syn_cnnc) dv_cache_0021 p0075
  have p0077 :=
    @g_peano5 x (syn_cdm F) (syn_cvv) dv_cache_0022
  have p0078 :=
    @g_syl3anc ph (.classMem (syn_cdm F) (syn_cvv)) (.classMem (syn_c0c) (syn_cdm F)) (syn_wral x (syn_cnnc) (.imp (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)))) (syn_wss (syn_cnnc) (syn_cdm F)) p0008 p0027 p0076 p0077
  have p0079 :=
    @g_eqssd ph (syn_cdm F) (syn_cnnc) p0004 p0078
  exact p0079

noncomputable def g_fnfreclem1
    (y : Var) (z : Var) (w : Var) (F : Class) (V : Class) (dv_F_w : w ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (.classMem F V) (.classMem (.cab w (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))))) (syn_cvv))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ({w} : Finset Var) ∪ F.fv ∪ V.fv
  have dv_cache_0001 : y ∉ ((Class.cv w)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_w_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (.cv y) (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_y_z), (Ne.symm dv_w_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_ccompl (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex w
  have p0001 :=
    @g_elcompl (.cv w) (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))) p0000
  have p0002 :=
    @g_elrn2 y (.cv w) (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))) dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_elrn2 z (syn_cop (.cv y) (.cv w)) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))) dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_eldif (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))
  have p0005 :=
    @g_elin (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))
  have p0006 :=
    @g_opelcnv (.cv y) (.cv w) F
  have p0007 :=
    @g_vex z
  have p0008 :=
    @g_opelxp (.cv z) (syn_cop (.cv y) (.cv w)) (syn_cvv) (syn_ccnv F)
  have p0009 :=
    @g_mpbiran (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cxp (syn_cvv) (syn_ccnv F))) (.classMem (.cv z) (syn_cvv)) (.classMem (syn_cop (.cv y) (.cv w)) (syn_ccnv F)) p0007 p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv w) F (.cv y))))
  have p0011 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv y) (.cv w)) (syn_ccnv F)) (.classMem (syn_cop (.cv w) (.cv y)) F) (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cxp (syn_cvv) (syn_ccnv F))) (syn_wbr (.cv w) F (.cv y)) p0006 p0009 p0010
  have p0012 :=
    @g_opelcnv (.cv z) (.cv w) F
  have p0013 :=
    @g_vex y
  have p0014 :=
    @g_otelins2 (.cv z) (.cv y) (.cv w) (syn_ccnv F) p0013
  have p0015 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv w) F (.cv z))))
  have p0016 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv z) (.cv w)) (syn_ccnv F)) (.classMem (syn_cop (.cv w) (.cv z)) F) (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins2 (syn_ccnv F))) (syn_wbr (.cv w) F (.cv z)) p0012 p0014 p0015
  have p0017 :=
    @g_anbi12i (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cxp (syn_cvv) (syn_ccnv F))) (syn_wbr (.cv w) F (.cv y)) (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins2 (syn_ccnv F))) (syn_wbr (.cv w) F (.cv z)) p0011 p0016
  have p0018 :=
    @g_bitri (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))) (syn_wa (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cxp (syn_cvv) (syn_ccnv F))) (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins2 (syn_ccnv F)))) (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) p0005 p0017
  have p0019 :=
    @g_otelins3 (.cv z) (.cv y) (.cv w) (syn_cid) p0000
  have p0020 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv z) (syn_cid) (.cv y))))
  have p0021 :=
    @g_ideq (.cv z) (.cv y) p0013
  have p0022 :=
    @g_equcom z y
  have p0023_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv z) (syn_cid) (.cv y)) (.objEq z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cid syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0021
  have p0023 :=
    @g_bitri (syn_wbr (.cv z) (syn_cid) (.cv y)) (.objEq z y) (.objEq y z) p0023_e00_recanon p0022
  have p0024 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins3 (syn_cid))) (.classMem (syn_cop (.cv z) (.cv y)) (syn_cid)) (syn_wbr (.cv z) (syn_cid) (.cv y)) (.objEq y z) p0019 p0020 p0023
  have p0025 :=
    @g_notbii (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins3 (syn_cid))) (.objEq y z) p0024
  have p0026 :=
    @g_anbi12i (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))) (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.neg (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins3 (syn_cid)))) (.neg (.objEq y z)) p0018 p0025
  have p0027 :=
    @g_bitri (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))) (syn_wa (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))) (.neg (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins3 (syn_cid))))) (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.neg (.objEq y z))) p0004 p0026
  have p0028 :=
    @g_exbii (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))) (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.neg (.objEq y z))) z p0027
  have p0029 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv w)) (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))) (syn_wex z (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))) (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.neg (.objEq y z)))) p0003 p0028
  have p0030 :=
    @g_exbii (.classMem (syn_cop (.cv y) (.cv w)) (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))) (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.neg (.objEq y z)))) y p0029
  have p0031 :=
    @g_exanali (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z) z
  have p0032 :=
    @g_exbii (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.neg (.objEq y z)))) (.neg (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)))) y p0031
  have p0033 :=
    @g_exnal (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))) y
  have p0034 :=
    @g_bitri (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.neg (.objEq y z))))) (syn_wex y (.neg (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))))) (.neg (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))))) p0032 p0033
  have p0035 :=
    @g_n_3bitrri (.classMem (.cv w) (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))))) (syn_wex y (.classMem (syn_cop (.cv y) (.cv w)) (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))))) (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.neg (.objEq y z))))) (.neg (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))))) p0002 p0030 p0034
  have p0036 :=
    @g_con1bii (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)))) (.classMem (.cv w) (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))))) p0035
  have p0037 :=
    @g_bitri (.classMem (.cv w) (syn_ccompl (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))))) (.neg (.classMem (.cv w) (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)))) p0001 p0036
  have p0038 :=
    @g_eqabi (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)))) w (syn_ccompl (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))))) dv_cache_0005 p0037
  have p0039 :=
    @g_vvex
  have p0040 :=
    @g_cnvexg F V
  have p0041 :=
    @g_xpexg (syn_cvv) (syn_ccnv F) (syn_cvv) (syn_cvv)
  have p0042 :=
    @g_sylancr (.classMem F V) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_ccnv F) (syn_cvv)) (.classMem (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cvv)) p0039 p0040 p0041
  have p0043 :=
    @g_ins2exg (syn_ccnv F) (syn_cvv)
  have p0044 :=
    @g_syl (.classMem F V) (.classMem (syn_ccnv F) (syn_cvv)) (.classMem (syn_cins2 (syn_ccnv F)) (syn_cvv)) p0040 p0043
  have p0045 :=
    @g_inexg (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)) (syn_cvv) (syn_cvv)
  have p0046 :=
    @g_syl2anc (.classMem F V) (.classMem (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cvv)) (.classMem (syn_cins2 (syn_ccnv F)) (syn_cvv)) (.classMem (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cvv)) p0042 p0044 p0045
  have p0047 :=
    @g_idex
  have p0048 :=
    @g_ins3ex (syn_cid) p0047
  have p0049 :=
    @g_difexg (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)) (syn_cvv) (syn_cvv)
  have p0050 :=
    @g_mpan2 (.classMem (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cvv)) (.classMem (syn_cins3 (syn_cid)) (syn_cvv)) (.classMem (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))) (syn_cvv)) p0048 p0049
  have p0051 :=
    @g_rnexg (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))) (syn_cvv)
  have p0052 :=
    @g_n_3syl (.classMem F V) (.classMem (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cvv)) (.classMem (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))) (syn_cvv)) (.classMem (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))) (syn_cvv)) p0046 p0050 p0051
  have p0053 :=
    @g_rnexg (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))) (syn_cvv)
  have p0054 :=
    @g_complexg (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))) (syn_cvv)
  have p0055 :=
    @g_n_3syl (.classMem F V) (.classMem (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))) (syn_cvv)) (.classMem (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid))))) (syn_cvv)) (.classMem (syn_ccompl (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))))) (syn_cvv)) p0052 p0053 p0054
  have p0056 :=
    @g_syl5eqelr (.classMem F V) (.cab w (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))))) (syn_ccompl (syn_crn (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cins3 (syn_cid)))))) (syn_cvv) p0038 p0055
  exact p0056

#print axioms g_fnfreclem1

end NFChoice.DirectNominalPrf.WPPReplay
