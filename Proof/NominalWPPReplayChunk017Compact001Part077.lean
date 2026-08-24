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
import NominalWPPReplayChunk017Compact001Part076

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

noncomputable def g_hnwcutreleq12dndv
    (ph : Wff) (D : Class) (R : Class) (S : Class) (E : Class) (hyp_hnwcutreleq12dndv_1 : Nominal.NPrf (.imp ph (.classEq R S))) (hyp_hnwcutreleq12dndv_2 : Nominal.NPrf (.imp ph (.classEq D E))) :
    Nominal.NPrf (.imp ph (.classEq (syn_chnwcutrel R D) (syn_chnwcutrel S E))) := by
  let proofSupport : Finset Var := ph.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  have p0000 :=
    @g_reseq2d ph R S (syn_cid) hyp_hnwcutreleq12dndv_1
  have p0001 :=
    @g_hnwcutimageeqdndv ph (syn_cres (syn_cid) R) (syn_cres (syn_cid) S) p0000
  have p0002 :=
    @g_coeq1d ph (syn_cimage (syn_cres (syn_cid) R)) (syn_cimage (syn_cres (syn_cid) S)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) p0001
  have p0003 :=
    @g_hnwcuttxpeq1dndv ph (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_ccom (syn_cimage (syn_cres (syn_cid) S)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid) p0002
  have p0004 :=
    (by simpa [syn_chnwcodefn] using (Nominal.classEqRefl (syn_chnwcodefn R)))
  have p0005 :=
    (by simpa [syn_chnwcodefn] using (Nominal.classEqRefl (syn_chnwcodefn S)))
  have p0006 :=
    @g_n_3eqtr4g ph (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) S)) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid)) (syn_chnwcodefn R) (syn_chnwcodefn S) p0003 p0004 p0005
  have p0007 :=
    @g_reseq2d ph D E (syn_cid) hyp_hnwcutreleq12dndv_2
  have p0008 :=
    @g_hnwcutimageeqdndv ph (syn_cres (syn_cid) D) (syn_cres (syn_cid) E) p0007
  have p0009 :=
    @g_difeq1d ph R S (syn_cid) hyp_hnwcutreleq12dndv_1
  have p0010 :=
    @g_cnveqd ph (syn_cdif R (syn_cid)) (syn_cdif S (syn_cid)) p0009
  have p0011 :=
    @g_hnwcutimageeqdndv ph (syn_ccnv (syn_cdif R (syn_cid))) (syn_ccnv (syn_cdif S (syn_cid))) p0010
  have p0012 :=
    @g_coeq12d ph (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_cres (syn_cid) E)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))) (syn_cimage (syn_ccnv (syn_cdif S (syn_cid)))) p0008 p0011
  have p0013 :=
    (by simpa [syn_chnwsegfn] using (Nominal.classEqRefl (syn_chnwsegfn R D)))
  have p0014 :=
    (by simpa [syn_chnwsegfn] using (Nominal.classEqRefl (syn_chnwsegfn S E)))
  have p0015 :=
    @g_n_3eqtr4g ph (syn_ccom (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))) (syn_ccom (syn_cimage (syn_cres (syn_cid) E)) (syn_cimage (syn_ccnv (syn_cdif S (syn_cid))))) (syn_chnwsegfn R D) (syn_chnwsegfn S E) p0012 p0013 p0014
  have p0016 :=
    @g_coeq12d ph (syn_chnwcodefn R) (syn_chnwcodefn S) (syn_chnwsegfn R D) (syn_chnwsegfn S E) p0006 p0015
  have p0017 :=
    (by simpa [syn_chnwcutfn] using (Nominal.classEqRefl (syn_chnwcutfn R D)))
  have p0018 :=
    (by simpa [syn_chnwcutfn] using (Nominal.classEqRefl (syn_chnwcutfn S E)))
  have p0019 :=
    @g_n_3eqtr4g ph (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D)) (syn_ccom (syn_chnwcodefn S) (syn_chnwsegfn S E)) (syn_chnwcutfn R D) (syn_chnwcutfn S E) p0016 p0017 p0018
  have p0020 :=
    @g_reseq1 (syn_chnwcutfn R D) (syn_chnwcutfn S E) (syn_cpw1 D)
  have p0021 :=
    @g_syl ph (.classEq (syn_chnwcutfn R D) (syn_chnwcutfn S E)) (.classEq (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (syn_cres (syn_chnwcutfn S E) (syn_cpw1 D))) p0019 p0020
  have p0022 :=
    @g_pw1eq D E
  have p0023 :=
    @g_syl ph (.classEq D E) (.classEq (syn_cpw1 D) (syn_cpw1 E)) hyp_hnwcutreleq12dndv_2 p0022
  have p0024 :=
    @g_reseq2d ph (syn_cpw1 D) (syn_cpw1 E) (syn_chnwcutfn S E) p0023
  have p0025 :=
    @g_eqtrd ph (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (syn_cres (syn_chnwcutfn S E) (syn_cpw1 D)) (syn_cres (syn_chnwcutfn S E) (syn_cpw1 E)) p0021 p0024
  have p0026 :=
    (by simpa [syn_chnwcutrel] using (Nominal.classEqRefl (syn_chnwcutrel R D)))
  have p0027 :=
    (by simpa [syn_chnwcutrel] using (Nominal.classEqRefl (syn_chnwcutrel S E)))
  have p0028 :=
    @g_n_3eqtr4g ph (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D)) (syn_cres (syn_chnwcutfn S E) (syn_cpw1 E)) (syn_chnwcutrel R D) (syn_chnwcutrel S E) p0025 p0026 p0027
  exact p0028

noncomputable def g_hnwcutcodeeq12clndv
    (C : Class) (D : Class) (R : Class) (S : Class) (E : Class) :
    Nominal.NPrf (.imp (.classMem C (syn_cvv)) (.imp (syn_wa (.classEq R S) (.classEq D E)) (.classEq (syn_chnwcutcode R D C) (syn_chnwcutcode S E C)))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint ((Class.cv x)).fv (S).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((Class.cv x)).fv (S).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((S).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (S).fv from (by exact fresh_x_not_S))))))
  have dv_cache_0003 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.imp (syn_wa (.classEq R S) (.classEq D E)) (.classEq (syn_chnwcutcode R D C) (syn_chnwcutcode S E C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_S, fresh_x_not_D, fresh_x_not_E, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_biid (syn_wa (.classEq R S) (.classEq D E))
  have p0001 :=
    @g_a1i (syn_wb (syn_wa (.classEq R S) (.classEq D E)) (syn_wa (.classEq R S) (.classEq D E))) (.classEq (.cv x) C) p0000
  have p0002 :=
    @g_hnwcutcodeeq3 (.cv x) C D R dv_cache_0001
  have p0003 :=
    @g_hnwcutcodeeq3 (.cv x) C E S dv_cache_0002
  have p0004 :=
    @g_eqeq12d (.classEq (.cv x) C) (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D C) (syn_chnwcutcode S E (.cv x)) (syn_chnwcutcode S E C) p0002 p0003
  have p0005 :=
    @g_imbi12d (.classEq (.cv x) C) (syn_wa (.classEq R S) (.classEq D E)) (syn_wa (.classEq R S) (.classEq D E)) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode S E (.cv x))) (.classEq (syn_chnwcutcode R D C) (syn_chnwcutcode S E C)) p0001 p0004
  have p0006 :=
    @g_hnwcutcodeeq12ndv x D R S E
  have p0007 :=
    @g_vtoclg (.imp (syn_wa (.classEq R S) (.classEq D E)) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode S E (.cv x)))) (.imp (syn_wa (.classEq R S) (.classEq D E)) (.classEq (syn_chnwcutcode R D C) (syn_chnwcutcode S E C))) x C (syn_cvv) dv_cache_0003 dv_cache_0004 p0005 p0006
  exact p0007

noncomputable def g_hnwcutambfactorvalimpclndv
    (A : Class) (B : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_B_q : q ∉ B.fv) (hyp_hnwcutambfactorvalimpclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_chwcn A)) (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ ((syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_q, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0001 :=
    @g_fveq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c2nd) p0000
  have p0002 :=
    @g_pw1eq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0003 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.classEq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) p0001 p0002
  have p0004 :=
    @g_pw1eq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))
  have p0005 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (.classEq (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) p0003 p0004
  have p0006 :=
    @g_eleq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (.cv q) p0005
  have p0007 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0008 :=
    @g_fveq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c1st) p0007
  have p0009 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0010 :=
    @g_fveq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c2nd) p0009
  have p0011 :=
    @g_hnwcutreleq12dndv (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) p0008 p0010
  have p0012 :=
    @g_sieqdndv (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)) (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) p0011
  have p0013 :=
    @g_coeq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (syn_chnqmap1 A) p0012
  have p0014 :=
    @g_fveq1d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv q) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) p0013
  have p0015 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0016 :=
    @g_fveq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c1st) p0015
  have p0017 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0018 :=
    @g_fveq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c2nd) p0017
  have p0019 :=
    @g_jca (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.classEq (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classEq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) p0016 p0018
  have p0020 :=
    @g_vex q
  have p0021 :=
    @g_uniex (.cv q) p0020
  have p0022 :=
    @g_uniex (syn_cuni (.cv q)) p0021
  have p0023 :=
    @g_hnwcutcodeeq12clndv (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_wa (.classEq (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classEq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (syn_cuni (syn_cuni (.cv q)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cuni (syn_cuni (.cv q))))) p0019 p0024
  have p0026 :=
    @g_eceq1 (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (syn_cuni (syn_cuni (.cv q)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)
  have p0027 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (syn_cuni (syn_cuni (.cv q)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cuni (syn_cuni (.cv q))))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) p0025 p0026
  have p0028 :=
    @g_eqeq12d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) p0014 p0027
  have p0029 :=
    @g_imbi12d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) p0006 p0028
  have p0030 :=
    @g_eqid (syn_c0)
  have p0031 :=
    @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_chwcn A))
  have p0032 :=
    @g_hncodecmpdefaultcnndv A
  have p0033 :=
    @g_a1i (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem B (syn_chwcn A)))) p0032
  have p0034 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A) p0031 p0033
  have p0035 :=
    Nominal.mp p0030 p0034
  have p0036 :=
    @g_hnwcutambfactorvalcodendv A (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) q dv_cache_0001 hyp_hnwcutambfactorvalimpclndv_1 p0035
  have p0037 :=
    @g_dedth (.classMem B (syn_chwcn A)) (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))) (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) p0029 p0036
  exact p0037

noncomputable def g_hnwcutambfactorvalimpndv
    (u : Var) (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_q_u : q ≠ u) (hyp_hnwcutambfactorvalimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_q_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutambfactorvalimpclndv A (.cv u) q dv_cache_0001 dv_cache_0002 hyp_hnwcutambfactorvalimpndv_1
  exact p0000

#print axioms g_hnwcutambfactorvalimpndv

end NFChoice.DirectNominalPrf.WPPReplay
