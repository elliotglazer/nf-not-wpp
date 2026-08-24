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
import NominalWPPReplayChunk017Compact001Part058

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

noncomputable def g_wpphitprefixtransferpackdndv
    (k : Var) (F : Class) (G : Class) (I : Class) (L : Class) (q : Var) (dv_F_q : q ∉ F.fv) (dv_G_q : q ∉ G.fv) (dv_I_q : q ∉ I.fv) (dv_L_q : q ∉ L.fv) (dv_k_q : k ≠ q) (hyp_wpphitprefixtransferpackdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wpphitprefixtransferpackdndv_2 : Nominal.NPrf (.classMem I (syn_cdm F))) (hyp_wpphitprefixtransferpackdndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wpphitprefixtransferpackdndv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wpphitprefixtransferpackdndv_5 : Nominal.NPrf (.classMem I (syn_cdm G))) (hyp_wpphitprefixtransferpackdndv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wpphitprefixtransferpackdndv_7 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv q)) (syn_clec) L)))) (hyp_wpphitprefixtransferpackdndv_8 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec G I) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv q))))))) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv k) (syn_cwpphit F I L)) (.classEq (syn_cfv (syn_cfrec G I) (.cv k)) (syn_cfv (syn_cfrec F I) (.cv k))))) := by
  let proofSupport : Finset Var := ({k} : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv ∪ L.fv ∪ ({q} : Finset Var)
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let z : Var := freshVar proofSupport 4
  let r : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_ne_k : n ≠ k := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_n : k ≠ n :=
    Ne.symm fresh_n_ne_k
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_not_I : n ∉ I.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_L : n ∉ L.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_q : n ≠ q := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_n : q ≠ n :=
    Ne.symm fresh_n_ne_q
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_k : x ≠ k := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_x : k ≠ x :=
    Ne.symm fresh_x_ne_k
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_L : x ∉ L.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_q : x ≠ q := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_ne_k : y ≠ k := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_y : k ≠ y :=
    Ne.symm fresh_y_ne_k
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_I : y ∉ I.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_L : y ∉ L.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_q : y ≠ q := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_ne_k : a ≠ k := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_a : k ≠ a :=
    Ne.symm fresh_a_ne_k
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_I : a ∉ I.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_L : a ∉ L.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_q : a ≠ q := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_a : q ≠ a :=
    Ne.symm fresh_a_ne_q
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_z_ne_k : z ≠ k := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_z : k ≠ z :=
    Ne.symm fresh_z_ne_k
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_I : z ∉ I.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_L : z ∉ L.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_q : z ≠ q := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_r_ne_k : r ≠ k := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_r : k ≠ r :=
    Ne.symm fresh_r_ne_k
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_r_not_G : r ∉ G.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_I : r ∉ I.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_L : r ∉ L.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_q : r ≠ q := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_r : q ≠ r :=
    Ne.symm fresh_r_ne_q
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_ne_k : b ≠ k := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_b : k ≠ b :=
    Ne.symm fresh_b_ne_k
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_b_not_G : b ∉ G.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_I : b ∉ I.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_L : b ∉ L.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_q : b ≠ q := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_b : q ≠ b :=
    Ne.symm fresh_b_ne_q
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_n_ne_y : n ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_n : y ≠ n :=
    Ne.symm fresh_n_ne_y
  have fresh_n_ne_a : n ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_n : a ≠ n :=
    Ne.symm fresh_n_ne_a
  have fresh_n_ne_z : n ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_z_ne_n : z ≠ n :=
    Ne.symm fresh_n_ne_z
  have fresh_n_ne_r : n ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_r_ne_n : r ≠ n :=
    Ne.symm fresh_n_ne_r
  have fresh_n_ne_b : n ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_b_ne_n : b ≠ n :=
    Ne.symm fresh_n_ne_b
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_r : x ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_r : y ≠ r := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_a_ne_z : a ≠ z := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_ne_r : a ≠ r := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_r_ne_a : r ≠ a :=
    Ne.symm fresh_a_ne_r
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_z_ne_r : z ≠ r := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_r_ne_z : r ≠ z :=
    Ne.symm fresh_z_ne_r
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_r_ne_b : r ≠ b := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_r : b ≠ r :=
    Ne.symm fresh_r_ne_b
  have dv_cache_0001 : x ∉ ((syn_cwppfrecprefixeq F G I k)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G, fresh_x_not_I, fresh_x_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (syn_c0c) (syn_cwppfrecprefixeq F G I k))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G, fresh_x_not_I, fresh_x_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) (syn_cwppfrecprefixeq F G I k))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_F, fresh_x_not_G, fresh_x_not_I, fresh_x_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : b ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show b ≠ r from (by exact fresh_b_ne_r))
  have dv_cache_0016 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0017 : b ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0018 : b ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show b ≠ z from (by exact fresh_b_ne_z))
  have dv_cache_0019 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0020 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0021 : r ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0022 : x ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ a from (by exact fresh_x_ne_a))
  have dv_cache_0023 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0024 : a ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0025 : r ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : b ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : r ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : b ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : r ∉ ((syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, fresh_r_ne_a, fresh_r_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : b ∉ ((syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : r ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show r ≠ b from (by exact fresh_r_ne_b))
  have dv_cache_0032 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : a ∉ ((syn_cplc (.cv y) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : z ∉ ((syn_cplc (.cv y) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : z ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : x ∉ ((Wff.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_a, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : z ∉ ((Wff.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : a ∉ ((Wff.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : x ∉ ((syn_cplc (.cv y) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0041 : a ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0042 : x ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_a, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0043 : z ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0044 : a ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_k, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0045 : q ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0046 : q ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0047 : q ∉ ((Wff.imp (.classMem (.cv y) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, dv_L_q, dv_G_q, dv_I_q, (Ne.symm dv_k_q), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0048 : q ∉ ((Wff.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_q, fresh_q_ne_y, dv_G_q, dv_I_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0049 : q ∉ ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, dv_G_q, dv_I_q, dv_L_q, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0050 : x ∉ ((Wff.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_F, fresh_x_not_G, fresh_x_not_I, fresh_x_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0051 : y ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_k, fresh_y_not_L, fresh_y_not_G, fresh_y_not_I, fresh_y_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0052 : y ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0053 : y ∉ ((Class.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, fresh_y_not_G, fresh_y_not_I, fresh_y_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0054 : x ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0055 : x ∉ ((Wff.classMem (.cv n) (syn_cwppfrecprefixeq F G I k))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, fresh_x_not_F, fresh_x_not_G, fresh_x_not_I, fresh_x_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0056 : n ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, fresh_n_not_L, fresh_n_not_G, fresh_n_not_I, fresh_n_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0057 : n ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0058 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0059 : n ∉ ((Wff.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv k)) (syn_cfv (syn_cfrec G I) (.cv k))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, fresh_n_not_F, fresh_n_not_I, fresh_n_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))
  have p0001 :=
    @g_simpr (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))
  have p0002 :=
    @g_simpl (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))
  have p0003 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))) (.classMem (.cv k) (syn_cwpphit G I L)) p0001 p0002
  have p0004 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0005 :=
    @g_elwpphitvndv L G I (.cv k)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_sylib (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv k)))) p0003 p0006
  have p0008 :=
    @g_simprd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv k))) p0007
  have p0009 :=
    @g_finlewe
  have p0010 :=
    @g_wppweref (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) p0011
  have p0013 :=
    @g_id (.classMem (.cv k) (syn_cnnc))
  have p0014 :=
    @g_refd (.classMem (.cv k) (syn_cnnc)) (syn_cnnc) (syn_ckqrel (syn_clefin)) (.cv k) p0012 p0013
  have p0015 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cnnc)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) p0000 p0014
  have p0016 :=
    @g_tru
  have p0017 :=
    @g_wppfrecprefixeqexndv k F G I hyp_wpphitprefixtransferpackdndv_1 hyp_wpphitprefixtransferpackdndv_4
  have p0018 :=
    @g_abid2 x (syn_cwppfrecprefixeq F G I k) dv_cache_0001
  have p0019 :=
    @g_eleq1i (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cwppfrecprefixeq F G I k) (syn_cvv) p0018
  have p0020 :=
    @g_mpbir (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_cwppfrecprefixeq F G I k) (syn_cvv)) p0017 p0019
  have p0021 :=
    @g_a1i (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) syn_wtru p0020
  have p0022 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpphitprefixtransferpackdndv_1 hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3
  have p0023 :=
    @g_wpporbit0ndv F I
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0026 :=
    @g_wpporbit0ndv G I
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_eqcomi (syn_cfv (syn_cfrec G I) (syn_c0c)) I p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_cfrec F I) (syn_c0c)) I (syn_cfv (syn_cfrec G I) (syn_c0c)) p0024 p0028
  have p0030 :=
    @g_a1i (.classEq (syn_cfv (syn_cfrec F I) (syn_c0c)) (syn_cfv (syn_cfrec G I) (syn_c0c))) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv k)) p0029
  have p0031 :=
    @g_peano1
  have p0032 :=
    @g_wppfrecprefixeqvalndv (syn_c0c) k F G I hyp_wpphitprefixtransferpackdndv_1 hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3 hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cwppfrecprefixeq F G I k)) (.imp (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (syn_c0c)) (syn_cfv (syn_cfrec G I) (syn_c0c)))) p0030 p0033
  have p0035 :=
    @g_a1i (.classMem (syn_c0c) (syn_cwppfrecprefixeq F G I k)) syn_wtru p0034
  have p0036 :=
    @g_n_0cex
  have p0037 :=
    @g_id (.classEq (.cv x) (syn_c0c))
  have p0038 :=
    @g_eleq1d (.classEq (.cv x) (syn_c0c)) (.cv x) (syn_c0c) (syn_cwppfrecprefixeq F G I k) p0037
  have p0039 :=
    @g_elab (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)) (.classMem (syn_c0c) (syn_cwppfrecprefixeq F G I k)) x (syn_c0c) dv_cache_0002 dv_cache_0003 p0036 p0038
  have p0040 :=
    @g_sylibr syn_wtru (.classMem (syn_c0c) (syn_cwppfrecprefixeq F G I k)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) p0035 p0039
  have p0041 :=
    @g_jca syn_wtru (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) p0021 p0040
  have p0042 :=
    @g_vex y
  have p0043 :=
    @g_id (.classEq (.cv x) (.cv y))
  have p0044 :=
    @g_eleq1d (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) (syn_cwppfrecprefixeq F G I k) p0043
  have p0045 :=
    @g_elab (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) x (.cv y) dv_cache_0004 dv_cache_0005 p0042 p0044
  have p0046 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpphitprefixtransferpackdndv_1 hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3
  have p0047 :=
    @g_a1i (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) p0046
  have p0048 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0049 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv y) (syn_cnnc)) p0047 p0048
  have p0050 :=
    @g_wpporbitsucndv F I (.cv y)
  have p0051 :=
    @g_syl (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv y) (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv y)))) p0049 p0050
  have p0052 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0053 :=
    @g_simp2 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0054 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) p0052 p0053
  have p0055 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0056 :=
    @g_simp3 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0057 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0055 p0056
  have p0058 :=
    @g_simpr (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0059 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0060 :=
    @g_finlewe
  have p0061 :=
    @g_wppweref (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) p0062
  have p0064 :=
    @g_id (.classMem (.cv y) (syn_cnnc))
  have p0065 :=
    @g_refd (.classMem (.cv y) (syn_cnnc)) (syn_cnnc) (syn_ckqrel (syn_clefin)) (.cv y) p0063 p0064
  have p0066 :=
    @g_orc (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c)))
  have p0067 :=
    @g_syl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c)))) p0065 p0066
  have p0068 :=
    @g_id (.classMem (.cv y) (syn_cnnc))
  have p0069 :=
    @g_id (.classMem (.cv y) (syn_cnnc))
  have p0070 :=
    @g_jca (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) p0068 p0069
  have p0071 :=
    @g_kqfinsucsplit (.cv y) (.cv y)
  have p0072 :=
    @g_syl (.classMem (.cv y) (syn_cnnc)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c))))) p0070 p0071
  have p0073 :=
    @g_mpbird (.classMem (.cv y) (syn_cnnc)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c)))) p0067 p0072
  have p0074 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) p0059 p0073
  have p0075 :=
    @g_a1d (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0074
  have p0076 :=
    @g_ancom (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
  have p0077 :=
    @g_finlewe
  have p0078 :=
    @g_wppwepo (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0079 :=
    Nominal.mp p0077 p0078
  have p0080 :=
    @g_porta (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0081 :=
    @g_mpbi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc)) (syn_w3a (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))) p0079 p0080
  have p0082 :=
    @g_simp2 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))
  have p0083 :=
    Nominal.mp p0081 p0082
  have p0084 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) p0083
  have p0085 :=
    @g_brex (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_ctrans)
  have p0086 :=
    @g_breq (.cv x) (.cv a) (.cv r) (syn_ckqrel (syn_clefin))
  have p0087 :=
    @g_breq (.cv a) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0088 :=
    @g_anbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0086 p0087
  have p0089 :=
    @g_breq (.cv x) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0090 :=
    @g_imbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) p0088 p0089
  have p0091 :=
    @g_ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) z (.cv b) dv_cache_0006 p0090
  have p0092 :=
    @g_n_2ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) x a (.cv b) (.cv b) dv_cache_0007 dv_cache_0008 p0091
  have p0093 :=
    @g_raleq (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) z (.cv b) (syn_cnnc) dv_cache_0009 dv_cache_0010
  have p0094 :=
    @g_raleqbi1dv (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) a (.cv b) (syn_cnnc) dv_cache_0011 dv_cache_0012 p0093
  have p0095 :=
    @g_raleqbi1dv (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))) x (.cv b) (syn_cnnc) dv_cache_0013 dv_cache_0014 p0094
  have p0096 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans x a z r b dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0097 :=
    @g_brabg (syn_wral x (.cv b) (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) (syn_wral x (.cv b) (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) r b (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cvv) (syn_cvv) (syn_ctrans) dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 p0092 p0095 p0096
  have p0098 :=
    @g_syl (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wa (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem (syn_cnnc) (syn_cvv))) (syn_wb (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))) p0085 p0097
  have p0099 :=
    @g_ibi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) p0098
  have p0100 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) p0084 p0099
  have p0101 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0102 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0103 :=
    @g_peano2 (.cv y)
  have p0104 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0102 p0103
  have p0105 :=
    @g_jca (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0101 p0104
  have p0106 :=
    @g_a1d (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) p0000
  have p0107 :=
    @g_pm3_2 (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc))
  have p0108 :=
    @g_syl9 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc))) p0106 p0107
  have p0109 :=
    @g_syl5 (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.imp (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc)))) p0105 p0108
  have p0110 :=
    @g_pm2_43d (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc))) p0109
  have p0111 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))))
  have p0112 :=
    @g_syl6ibr (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) p0110 p0111
  have p0113 :=
    @g_breq1 (.cv x) (.cv y) (.cv a) (syn_ckqrel (syn_clefin))
  have p0114 :=
    @g_anbi1d (.classEq (.cv x) (.cv y)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0113
  have p0115 :=
    @g_breq1 (.cv x) (.cv y) (.cv z) (syn_ckqrel (syn_clefin))
  have p0116 :=
    @g_imbi12d (.classEq (.cv x) (.cv y)) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) p0114 p0115
  have p0117 :=
    @g_breq2 (.cv a) (syn_cplc (.cv y) (syn_c1c)) (.cv y) (syn_ckqrel (syn_clefin))
  have p0118 :=
    @g_breq1 (.cv a) (syn_cplc (.cv y) (syn_c1c)) (.cv z) (syn_ckqrel (syn_clefin))
  have p0119 :=
    @g_anbi12d (.classEq (.cv a) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) p0117 p0118
  have p0120 :=
    @g_imbi1d (.classEq (.cv a) (syn_cplc (.cv y) (syn_c1c))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) p0119
  have p0121 :=
    @g_breq2 (.cv z) (.cv k) (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin))
  have p0122 :=
    @g_anbi2d (.classEq (.cv z) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) p0121
  have p0123 :=
    @g_breq2 (.cv z) (.cv k) (.cv y) (syn_ckqrel (syn_clefin))
  have p0124 :=
    @g_imbi12d (.classEq (.cv z) (.cv k)) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0122 p0123
  have p0125 :=
    @g_rspc3v (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))) x a z (.cv y) (syn_cplc (.cv y) (syn_c1c)) (.cv k) (syn_cnnc) (syn_cnnc) (syn_cnnc) dv_cache_0004 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0014 dv_cache_0014 dv_cache_0012 dv_cache_0014 dv_cache_0012 dv_cache_0010 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0116 p0120 p0124
  have p0126 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.imp (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))) p0112 p0125
  have p0127 :=
    @g_mpdi (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0100 p0126
  have p0128 :=
    @g_syl7bi (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0076 p0127
  have p0129 :=
    @g_exp4a (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0128
  have p0130 :=
    Nominal.ax2 (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0131 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))) (.imp (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))) p0129 p0130
  have p0132 :=
    @g_mpdi (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0075 p0131
  have p0133 :=
    @g_mpdi (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0058 p0132
  have p0134 :=
    @g_syl5 (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0057 p0133
  have p0135 :=
    @g_pm3_2 (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0136 :=
    @g_syl9 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0134 p0135
  have p0137 :=
    @g_syl5 (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.imp (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))) p0054 p0136
  have p0138 :=
    @g_pm2_43d (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0137
  have p0139 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))))
  have p0140 :=
    @g_syl6ibr (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0138 p0139
  have p0141 :=
    @g_wppfrecprefixeqvalndv (.cv y) k F G I hyp_wpphitprefixtransferpackdndv_1 hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3 hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0142 :=
    @g_biimpd (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv y)))) p0141
  have p0143 :=
    @g_n_3imp (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv y))) p0142
  have p0144 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec F I) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv y))) p0140 p0143
  have p0145 :=
    @g_fveq2 (syn_cfv (syn_cfrec F I) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv y)) F
  have p0146 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec F I) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv y))) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv y))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y)))) p0144 p0145
  have p0147 :=
    @g_eqeq2 (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv y))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c)))
  have p0148 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv y))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y)))) (syn_wb (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))))) p0146 p0147
  have p0149 :=
    @g_bi1 (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))))
  have p0150 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wb (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))))) (.imp (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))))) p0148 p0149
  have p0151 :=
    @g_mpdi (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y)))) p0051 p0150
  have p0152 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0153 :=
    @g_simp3 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0154 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0152 p0153
  have p0155 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0156 :=
    @g_kqfinsucnle (.cv y)
  have p0157 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) p0155 p0156
  have p0158 :=
    @g_notnot2 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0159 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0160 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0161 :=
    @g_simpr (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0162 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0160 p0161
  have p0163 :=
    @g_a1d (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) p0162
  have p0164 :=
    @g_ancom (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0165 :=
    @g_finlewe
  have p0166 :=
    @g_wppwepo (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0167 :=
    Nominal.mp p0165 p0166
  have p0168 :=
    @g_porta (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0169 :=
    @g_mpbi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc)) (syn_w3a (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))) p0167 p0168
  have p0170 :=
    @g_simp2 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))
  have p0171 :=
    Nominal.mp p0169 p0170
  have p0172 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0171
  have p0173 :=
    @g_brex (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_ctrans)
  have p0174 :=
    @g_breq (.cv x) (.cv a) (.cv r) (syn_ckqrel (syn_clefin))
  have p0175 :=
    @g_breq (.cv a) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0176 :=
    @g_anbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0174 p0175
  have p0177 :=
    @g_breq (.cv x) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0178 :=
    @g_imbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) p0176 p0177
  have p0179 :=
    @g_ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) z (.cv b) dv_cache_0006 p0178
  have p0180 :=
    @g_n_2ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) x a (.cv b) (.cv b) dv_cache_0007 dv_cache_0008 p0179
  have p0181 :=
    @g_raleq (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) z (.cv b) (syn_cnnc) dv_cache_0009 dv_cache_0010
  have p0182 :=
    @g_raleqbi1dv (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) a (.cv b) (syn_cnnc) dv_cache_0011 dv_cache_0012 p0181
  have p0183 :=
    @g_raleqbi1dv (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))) x (.cv b) (syn_cnnc) dv_cache_0013 dv_cache_0014 p0182
  have p0184 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans x a z r b dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0185 :=
    @g_brabg (syn_wral x (.cv b) (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) (syn_wral x (.cv b) (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) r b (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cvv) (syn_cvv) (syn_ctrans) dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 p0180 p0183 p0184
  have p0186 :=
    @g_syl (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wa (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem (syn_cnnc) (syn_cvv))) (syn_wb (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))) p0173 p0185
  have p0187 :=
    @g_ibi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) p0186
  have p0188 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) p0172 p0187
  have p0189 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0190 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0191 :=
    @g_peano2 (.cv y)
  have p0192 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0190 p0191
  have p0193 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0189 p0192
  have p0194 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0195 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cnnc)) p0194 p0106
  have p0196 :=
    @g_pm3_2 (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0197 :=
    @g_syl9 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) p0195 p0196
  have p0198 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.imp (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))) p0193 p0197
  have p0199 :=
    @g_pm2_43d (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) p0198
  have p0200 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0201 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0202 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) p0200 p0201
  have p0203 :=
    @g_pm3_2 (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc))
  have p0204 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.classMem (.cv y) (syn_cnnc)) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc))) p0202 p0203
  have p0205 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.imp (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)))) p0199 p0204
  have p0206 :=
    @g_pm2_43d (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc))) p0205
  have p0207 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))))
  have p0208 :=
    @g_syl6ibr (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc))) (syn_w3a (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) p0206 p0207
  have p0209 :=
    @g_breq1 (.cv x) (syn_cplc (.cv y) (syn_c1c)) (.cv a) (syn_ckqrel (syn_clefin))
  have p0210 :=
    @g_anbi1d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0209
  have p0211 :=
    @g_breq1 (.cv x) (syn_cplc (.cv y) (syn_c1c)) (.cv z) (syn_ckqrel (syn_clefin))
  have p0212 :=
    @g_imbi12d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) p0210 p0211
  have p0213 :=
    @g_breq2 (.cv a) (.cv k) (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin))
  have p0214 :=
    @g_breq1 (.cv a) (.cv k) (.cv z) (syn_ckqrel (syn_clefin))
  have p0215 :=
    @g_anbi12d (.classEq (.cv a) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)) p0213 p0214
  have p0216 :=
    @g_imbi1d (.classEq (.cv a) (.cv k)) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) p0215
  have p0217 :=
    @g_breq2 (.cv z) (.cv y) (.cv k) (syn_ckqrel (syn_clefin))
  have p0218 :=
    @g_anbi2d (.classEq (.cv z) (.cv y)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0217
  have p0219 :=
    @g_breq2 (.cv z) (.cv y) (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin))
  have p0220 :=
    @g_imbi12d (.classEq (.cv z) (.cv y)) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0218 p0219
  have p0221 :=
    @g_rspc3v (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) x a z (syn_cplc (.cv y) (syn_c1c)) (.cv k) (.cv y) (syn_cnnc) (syn_cnnc) (syn_cnnc) dv_cache_0040 dv_cache_0034 dv_cache_0035 dv_cache_0041 dv_cache_0036 dv_cache_0033 dv_cache_0014 dv_cache_0014 dv_cache_0012 dv_cache_0014 dv_cache_0012 dv_cache_0010 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0212 p0216 p0220
  have p0222 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_w3a (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.imp (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))) p0208 p0221
  have p0223 :=
    @g_mpdi (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) p0188 p0222
  have p0224 :=
    @g_syl7bi (syn_wa (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0164 p0223
  have p0225 :=
    @g_exp4a (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0224
  have p0226 :=
    Nominal.ax2 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0227 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))) (.imp (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))) p0225 p0226
  have p0228 :=
    @g_mpdi (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) p0163 p0227
  have p0229 :=
    @g_mpdi (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0159 p0228
  have p0230 :=
    @g_exp3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0229
  have p0231 :=
    @g_syl7 (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0158 p0230
  have p0232 :=
    @g_notnot1 (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0233 :=
    @g_syl8 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) (.neg (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))) p0231 p0232
  have p0234 :=
    Nominal.ax3 (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
  have p0235 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) (.neg (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))))) (.imp (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) p0233 p0234
  have p0236 :=
    @g_mpdi (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0157 p0235
  have p0237 :=
    @g_notnot2 (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))
  have p0238 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0239 :=
    @g_pm3_2 (.classMem (.cv y) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))
  have p0240 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0241 :=
    @g_elwpphitvndv L G I (.cv y)
  have p0242 :=
    Nominal.mp p0240 p0241
  have p0243 :=
    @g_biimpri (.classMem (.cv y) (syn_cwpphit G I L)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) p0242
  have p0244 :=
    @g_syl6 (.classMem (.cv y) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) (.classMem (.cv y) (syn_cwpphit G I L)) p0239 p0243
  have p0245 :=
    @g_simpr (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))
  have p0246 :=
    @g_simpr (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))
  have p0247 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))) p0245 p0246
  have p0248 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0249 :=
    @g_eleq1d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cwpphit G I L) p0248
  have p0250 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0251 :=
    @g_breq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (.cv k) (syn_ckqrel (syn_clefin)) p0250
  have p0252 :=
    @g_imbi12d (.classEq (.cv q) (.cv y)) (.classMem (.cv q) (syn_cwpphit G I L)) (.classMem (.cv y) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) p0249 p0251
  have p0253 :=
    @g_rspcv (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))) (.imp (.classMem (.cv y) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) q (.cv y) (syn_cnnc) dv_cache_0045 dv_cache_0046 dv_cache_0047 p0252
  have p0254 :=
    @g_syl5com (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))) (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0247 p0253
  have p0255 :=
    @g_a1dd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) p0254
  have p0256 :=
    Nominal.ax2 (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) (.classMem (.cv y) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0257 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv y) (syn_cnnc)) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) (.imp (.classMem (.cv y) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) (.imp (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) (.classMem (.cv y) (syn_cwpphit G I L))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) p0255 p0256
  have p0258 :=
    @g_mpdi (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv y) (syn_cnnc)) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) (.classMem (.cv y) (syn_cwpphit G I L))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0244 p0257
  have p0259 :=
    @g_syl5 (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0238 p0258
  have p0260 :=
    @g_syl7 (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) p0237 p0259
  have p0261 :=
    @g_notnot1 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0262 :=
    @g_syl8 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) p0260 p0261
  have p0263 :=
    Nominal.ax3 (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))
  have p0264 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))))) (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))))) (.imp (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))))) p0262 p0263
  have p0265 :=
    @g_mpdd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) p0236 p0264
  have p0266 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0267 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0268 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec G I) p0267
  have p0269 :=
    @g_breq2d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv q)) (syn_cfv (syn_cfrec G I) (.cv y)) L (syn_clec) p0268
  have p0270 :=
    @g_notbid (.classEq (.cv q) (.cv y)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv q))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y))) p0269
  have p0271 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0272 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec G I) p0271
  have p0273 :=
    @g_breq1d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv q)) (syn_cfv (syn_cfrec G I) (.cv y)) L (syn_clec) p0272
  have p0274 :=
    @g_imbi12d (.classEq (.cv q) (.cv y)) (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv q)))) (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv q)) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L) p0270 p0273
  have p0275 :=
    @g_rspcv (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv q)) (syn_clec) L)) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L)) q (.cv y) (syn_cnnc) dv_cache_0045 dv_cache_0046 dv_cache_0048 p0274
  have p0276 :=
    @g_mpi (.classMem (.cv y) (syn_cnnc)) (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv q)) (syn_clec) L))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L)) hyp_wpphitprefixtransferpackdndv_7 p0275
  have p0277 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L)) p0266 p0276
  have p0278 :=
    @g_sylcom (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L) p0265 p0277
  have p0279 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0280 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0281 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec G I) p0280
  have p0282 :=
    @g_breq1d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv q)) (syn_cfv (syn_cfrec G I) (.cv y)) L (syn_clec) p0281
  have p0283 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0284 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec G I) p0283
  have p0285 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv q)) (syn_cfv (syn_cfrec G I) (.cv y)) F p0284
  have p0286 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0287 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec G I) p0286
  have p0288 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec G I) (.cv q)) (syn_cfv (syn_cfrec G I) (.cv y)) G p0287
  have p0289 :=
    @g_eqeq12d (.classEq (.cv q) (.cv y)) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))) p0285 p0288
  have p0290 :=
    @g_imbi12d (.classEq (.cv q) (.cv y)) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv q)) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv q)))) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y)))) p0282 p0289
  have p0291 :=
    @g_rspcv (.imp (syn_wbr (syn_cfv (syn_cfrec G I) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv q))))) (.imp (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))))) q (.cv y) (syn_cnnc) dv_cache_0045 dv_cache_0046 dv_cache_0049 p0290
  have p0292 :=
    @g_mpi (.classMem (.cv y) (syn_cnnc)) (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec G I) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv q)))))) (.imp (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))))) hyp_wpphitprefixtransferpackdndv_8 p0291
  have p0293 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.imp (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))))) p0279 p0292
  have p0294 :=
    @g_sylcom (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cfv (syn_cfrec G I) (.cv y)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y)))) p0278 p0293
  have p0295 :=
    @g_syl5 (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y)))) p0154 p0294
  have p0296 :=
    @g_eqeq2 (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c)))
  have p0297 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y)))) (syn_wb (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))))) p0295 p0296
  have p0298 :=
    @g_bi1 (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))))
  have p0299 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wb (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))))) (.imp (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))))) p0297 p0298
  have p0300 :=
    @g_mpdd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec G I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y)))) p0151 p0299
  have p0301 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0302 :=
    @g_a1i (syn_w3a (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) p0301
  have p0303 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0304 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))) (.classMem (.cv y) (syn_cnnc)) p0302 p0303
  have p0305 :=
    @g_wpporbitsucndv G I (.cv y)
  have p0306 :=
    @g_syl (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_w3a (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G))) (.classMem (.cv y) (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y)))) p0304 p0305
  have p0307 :=
    @g_eqcomd (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))) p0306
  have p0308 :=
    @g_eqeq2d (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y))) (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) p0307
  have p0309 :=
    @g_mpbidi (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv G (syn_cfv (syn_cfrec G I) (.cv y)))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c)))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) p0300 p0308
  have p0310 :=
    @g_n_3expd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c)))) p0309
  have p0311 :=
    @g_peano2 (.cv y)
  have p0312 :=
    @g_wppfrecprefixeqvalndv (syn_cplc (.cv y) (syn_c1c)) k F G I hyp_wpphitprefixtransferpackdndv_1 hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3 hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0313 :=
    @g_syl (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (syn_wb (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c)))))) p0311 p0312
  have p0314 :=
    @g_biimprd (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c))))) p0313
  have p0315 :=
    @g_a1d (.classMem (.cv y) (syn_cnnc)) (.imp (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c))))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k))) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) p0314
  have p0316 :=
    @g_a2d (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c))))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k)) p0315
  have p0317 :=
    @g_sylcom (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec G I) (syn_cplc (.cv y) (syn_c1c)))))) (.imp (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k))) p0310 p0316
  have p0318 :=
    @g_adantrd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k))) syn_wtru p0317
  have p0319 :=
    @g_syl7bi (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (.cv y) (syn_cwppfrecprefixeq F G I k)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) syn_wtru) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k)) p0045 p0318
  have p0320 :=
    @g_n_1cex
  have p0321 :=
    @g_addcex (.cv y) (syn_c1c) p0042 p0320
  have p0322 :=
    @g_id (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
  have p0323 :=
    @g_eleq1d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.cv x) (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k) p0322
  have p0324 :=
    @g_elab (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k)) x (syn_cplc (.cv y) (syn_c1c)) dv_cache_0040 dv_cache_0050 p0321 p0323
  have p0325 :=
    @g_biimpri (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k)) p0324
  have p0326 :=
    @g_syl8 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) syn_wtru) (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq F G I k)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) p0319 p0325
  have p0327 :=
    @g_ancomsd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv y) (syn_cnnc)) syn_wtru (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) p0326
  have p0328 :=
    @g_exp3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) syn_wtru (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) p0327
  have p0329 :=
    @g_ralrimdv (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) syn_wtru (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) y (syn_cnnc) dv_cache_0051 dv_cache_0052 p0328
  have p0330 :=
    @g_pm3_2 (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))))
  have p0331 :=
    @g_syl9 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) syn_wtru (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))))) (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) (syn_wa (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))))) p0329 p0330
  have p0332 :=
    @g_syl5 syn_wtru (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.imp syn_wtru (syn_wa (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))))))) p0041 p0331
  have p0333 :=
    @g_pm2_43d (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) syn_wtru (syn_wa (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))))) p0332
  have p0334 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))))))))
  have p0335 :=
    @g_syl6ibr (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) syn_wtru (syn_wa (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))))) (syn_w3a (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))))) p0333 p0334
  have p0336 :=
    @g_peano5 y (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv) dv_cache_0053
  have p0337 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) syn_wtru (syn_w3a (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))))) (syn_wss (syn_cnnc) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) p0335 p0336
  have p0338 :=
    @g_ssel (syn_cnnc) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))) (.cv n)
  have p0339 :=
    @g_syl6 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) syn_wtru (syn_wss (syn_cnnc) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.imp (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k))))) p0337 p0338
  have p0340 :=
    @g_com23 (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) syn_wtru (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) p0339
  have p0341 :=
    @g_imp3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv n) (syn_cnnc)) syn_wtru (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) p0340
  have p0342 :=
    @g_id (.classEq (.cv x) (.cv n))
  have p0343 :=
    @g_eleq1d (.classEq (.cv x) (.cv n)) (.cv x) (.cv n) (syn_cwppfrecprefixeq F G I k) p0342
  have p0344 :=
    @g_elabg (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)) (.classMem (.cv n) (syn_cwppfrecprefixeq F G I k)) x (.cv n) (syn_cnnc) dv_cache_0054 dv_cache_0055 p0343
  have p0345 :=
    @g_adantr (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (.cv n) (syn_cwppfrecprefixeq F G I k))) syn_wtru p0344
  have p0346 :=
    @g_mpbidi (syn_wa (.classMem (.cv n) (syn_cnnc)) syn_wtru) (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq F G I k)))) (.classMem (.cv n) (syn_cwppfrecprefixeq F G I k)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) p0341 p0345
  have p0347 :=
    @g_mpan2i (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv n) (syn_cnnc)) syn_wtru (.classMem (.cv n) (syn_cwppfrecprefixeq F G I k)) p0016 p0346
  have p0348 :=
    @g_wppfrecprefixeqvalndv (.cv n) k F G I hyp_wpphitprefixtransferpackdndv_1 hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3 hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0349 :=
    @g_mpbidi (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwppfrecprefixeq F G I k)) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n)))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) p0347 p0348
  have p0350 :=
    @g_ralrimiv (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n)))) n (syn_cnnc) dv_cache_0056 p0349
  have p0351 :=
    @g_id (.classEq (.cv n) (.cv k))
  have p0352 :=
    @g_breq1d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (.cv k) (syn_ckqrel (syn_clefin)) p0351
  have p0353 :=
    @g_id (.classEq (.cv n) (.cv k))
  have p0354 :=
    @g_fveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (syn_cfrec F I) p0353
  have p0355 :=
    @g_id (.classEq (.cv n) (.cv k))
  have p0356 :=
    @g_fveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (syn_cfrec G I) p0355
  have p0357 :=
    @g_eqeq12d (.classEq (.cv n) (.cv k)) (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec F I) (.cv k)) (syn_cfv (syn_cfrec G I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv k)) p0354 p0356
  have p0358 :=
    @g_imbi12d (.classEq (.cv n) (.cv k)) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))) (.classEq (syn_cfv (syn_cfrec F I) (.cv k)) (syn_cfv (syn_cfrec G I) (.cv k))) p0352 p0357
  have p0359 :=
    @g_rspcv (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n)))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv k)) (syn_cfv (syn_cfrec G I) (.cv k)))) n (.cv k) (syn_cnnc) dv_cache_0057 dv_cache_0058 dv_cache_0059 p0358
  have p0360 :=
    @g_syl5com (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wral n (syn_cnnc) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))))) (.classMem (.cv k) (syn_cnnc)) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv k)) (syn_cfv (syn_cfrec G I) (.cv k)))) p0350 p0359
  have p0361 :=
    @g_mpd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cnnc)) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv k)) (syn_cfv (syn_cfrec G I) (.cv k)))) p0000 p0360
  have p0362 :=
    @g_mpd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) (.cv k)) (syn_cfv (syn_cfrec G I) (.cv k))) p0015 p0361
  have p0363 :=
    @g_eqcomd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_cfv (syn_cfrec F I) (.cv k)) (syn_cfv (syn_cfrec G I) (.cv k)) p0362
  have p0364 :=
    @g_breq2d (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_cfv (syn_cfrec G I) (.cv k)) (syn_cfv (syn_cfrec F I) (.cv k)) L (syn_clec) p0363
  have p0365 :=
    @g_mpbid (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G I) (.cv k))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv k))) p0008 p0364
  have p0366 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv k))) p0000 p0365
  have p0367 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpphitprefixtransferpackdndv_1 hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3
  have p0368 :=
    @g_elwpphitvndv L F I (.cv k)
  have p0369 :=
    Nominal.mp p0367 p0368
  have p0370 :=
    @g_sylibr (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv k)))) (.classMem (.cv k) (syn_cwpphit F I L)) p0366 p0369
  have p0371 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G I L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cwpphit F I L)) (.classEq (syn_cfv (syn_cfrec G I) (.cv k)) (syn_cfv (syn_cfrec F I) (.cv k))) p0370 p0363
  exact p0371

#print axioms g_wpphitprefixtransferpackdndv

end NFChoice.DirectNominalPrf.WPPReplay
