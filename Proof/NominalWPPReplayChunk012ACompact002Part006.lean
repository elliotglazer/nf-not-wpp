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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk012ACompact002Part005

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

noncomputable def g_fsn2
    (A : Class) (B : Class) (F : Class) (hyp_fsn2_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wf F (syn_csn A) B) (syn_wa (.classMem (syn_cfv F A) B) (.classEq F (syn_csn (syn_cop A (syn_cfv F A)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_snid A hyp_fsn2_1
  have p0001 :=
    @g_ffvelrn (syn_csn A) B A F
  have p0002 :=
    @g_mpan2 (syn_wf F (syn_csn A) B) (.classMem A (syn_csn A)) (.classMem (syn_cfv F A) B) p0000 p0001
  have p0003 :=
    @g_ffn (syn_csn A) B F
  have p0004 :=
    @g_dffn3 (syn_csn A) F
  have p0005 :=
    @g_biimpi (syn_wfn F (syn_csn A)) (syn_wf F (syn_csn A) (syn_crn F)) p0004
  have p0006 :=
    @g_imadmrn F
  have p0007 :=
    @g_fndm (syn_csn A) F
  have p0008 :=
    @g_imaeq2d (syn_wfn F (syn_csn A)) (syn_cdm F) (syn_csn A) F p0007
  have p0009 :=
    @g_syl5eqr (syn_wfn F (syn_csn A)) (syn_crn F) (syn_cima F (syn_cdm F)) (syn_cima F (syn_csn A)) p0006 p0008
  have p0010 :=
    @g_fnsnfv (syn_csn A) A F
  have p0011 :=
    @g_mpan2 (syn_wfn F (syn_csn A)) (.classMem A (syn_csn A)) (.classEq (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A))) p0000 p0010
  have p0012 :=
    @g_eqtr4d (syn_wfn F (syn_csn A)) (syn_crn F) (syn_cima F (syn_csn A)) (syn_csn (syn_cfv F A)) p0009 p0011
  have p0013 :=
    @g_feq3 (syn_crn F) (syn_csn (syn_cfv F A)) (syn_csn A) F
  have p0014 :=
    @g_syl (syn_wfn F (syn_csn A)) (.classEq (syn_crn F) (syn_csn (syn_cfv F A))) (syn_wb (syn_wf F (syn_csn A) (syn_crn F)) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A)))) p0012 p0013
  have p0015 :=
    @g_mpbid (syn_wfn F (syn_csn A)) (syn_wf F (syn_csn A) (syn_crn F)) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) p0005 p0014
  have p0016 :=
    @g_syl (syn_wf F (syn_csn A) B) (syn_wfn F (syn_csn A)) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) p0003 p0015
  have p0017 :=
    @g_jca (syn_wf F (syn_csn A) B) (.classMem (syn_cfv F A) B) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) p0002 p0016
  have p0018 :=
    @g_snssi (syn_cfv F A) B
  have p0019 :=
    @g_fss (syn_csn A) (syn_csn (syn_cfv F A)) B F
  have p0020 :=
    @g_ancoms (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) (syn_wss (syn_csn (syn_cfv F A)) B) (syn_wf F (syn_csn A) B) p0019
  have p0021 :=
    @g_sylan (.classMem (syn_cfv F A) B) (syn_wss (syn_csn (syn_cfv F A)) B) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) (syn_wf F (syn_csn A) B) p0018 p0020
  have p0022 :=
    @g_impbii (syn_wf F (syn_csn A) B) (syn_wa (.classMem (syn_cfv F A) B) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A)))) p0017 p0021
  have p0023 :=
    @g_fvex A F
  have p0024 :=
    @g_fsn A (syn_cfv F A) F hyp_fsn2_1 p0023
  have p0025 :=
    @g_anbi2i (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A))) (.classEq F (syn_csn (syn_cop A (syn_cfv F A)))) (.classMem (syn_cfv F A) B) p0024
  have p0026 :=
    @g_bitri (syn_wf F (syn_csn A) B) (syn_wa (.classMem (syn_cfv F A) B) (syn_wf F (syn_csn A) (syn_csn (syn_cfv F A)))) (syn_wa (.classMem (syn_cfv F A) B) (.classEq F (syn_csn (syn_cop A (syn_cfv F A))))) p0022 p0025
  exact p0026

noncomputable def g_ressnop0
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.neg (.classMem A C)) (.classEq (syn_cres (syn_csn (syn_cop A B)) C) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_opelxp A B C (syn_cvv)
  have p0001 :=
    @g_simplbi (.classMem (syn_cop A B) (syn_cxp C (syn_cvv))) (.classMem A C) (.classMem B (syn_cvv)) p0000
  have p0002 :=
    @g_con3i (.classMem (syn_cop A B) (syn_cxp C (syn_cvv))) (.classMem A C) p0001
  have p0003 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres (syn_csn (syn_cop A B)) C)))
  have p0004 :=
    @g_incom (syn_csn (syn_cop A B)) (syn_cxp C (syn_cvv))
  have p0005 :=
    @g_eqtri (syn_cres (syn_csn (syn_cop A B)) C) (syn_cin (syn_csn (syn_cop A B)) (syn_cxp C (syn_cvv))) (syn_cin (syn_cxp C (syn_cvv)) (syn_csn (syn_cop A B))) p0003 p0004
  have p0006 :=
    @g_disjsn (syn_cxp C (syn_cvv)) (syn_cop A B)
  have p0007 :=
    @g_biimpri (.classEq (syn_cin (syn_cxp C (syn_cvv)) (syn_csn (syn_cop A B))) (syn_c0)) (.neg (.classMem (syn_cop A B) (syn_cxp C (syn_cvv)))) p0006
  have p0008 :=
    @g_syl5eq (.neg (.classMem (syn_cop A B) (syn_cxp C (syn_cvv)))) (syn_cres (syn_csn (syn_cop A B)) C) (syn_cin (syn_cxp C (syn_cvv)) (syn_csn (syn_cop A B))) (syn_c0) p0005 p0007
  have p0009 :=
    @g_syl (.neg (.classMem A C)) (.neg (.classMem (syn_cop A B) (syn_cxp C (syn_cvv)))) (.classEq (syn_cres (syn_csn (syn_cop A B)) C) (syn_c0)) p0002 p0008
  exact p0009

noncomputable def g_fvconst
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf F A (syn_csn B)) (.classMem C A)) (.classEq (syn_cfv F C) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_ffvelrn A (syn_csn B) C F
  have p0001 :=
    @g_elsni (syn_cfv F C) B
  have p0002 :=
    @g_syl (syn_wa (syn_wf F A (syn_csn B)) (.classMem C A)) (.classMem (syn_cfv F C) (syn_csn B)) (.classEq (syn_cfv F C) B) p0000 p0001
  exact p0002

noncomputable def g_fvi
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (syn_cfv (syn_cid) A) A)) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (syn_cfv (syn_cid) A) A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fveq2 (.cv x) A (syn_cid)
  have p0001 :=
    @g_id (.classEq (.cv x) A)
  have p0002 :=
    @g_eqeq12d (.classEq (.cv x) A) (syn_cfv (syn_cid) (.cv x)) (syn_cfv (syn_cid) A) (.cv x) A p0000 p0001
  have p0003 :=
    @g_funi
  have p0004 :=
    @g_dmi
  have p0005 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_cid) (syn_cvv))))
  have p0006 :=
    @g_mpbir2an (syn_wfn (syn_cid) (syn_cvv)) (syn_wfun (syn_cid)) (.classEq (syn_cdm (syn_cid)) (syn_cvv)) p0003 p0004 p0005
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_equid x
  have p0009 :=
    @g_ideq (.cv x) (.cv x) p0007
  have p0010 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv x))))
  have p0011_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv x)) (.objEq x x)) :=
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
      p0009
  have p0011 :=
    @g_bitr3i (.objEq x x) (syn_wbr (.cv x) (syn_cid) (.cv x)) (.classMem (syn_cop (.cv x) (.cv x)) (syn_cid)) p0011_e00_recanon p0010
  have p0012 :=
    @g_mpbi (.objEq x x) (.classMem (syn_cop (.cv x) (.cv x)) (syn_cid)) p0008 p0011
  have p0013 :=
    @g_fnopfvb (syn_cvv) (.cv x) (.cv x) (syn_cid)
  have p0014 :=
    @g_mpbiri (syn_wa (syn_wfn (syn_cid) (syn_cvv)) (.classMem (.cv x) (syn_cvv))) (.classEq (syn_cfv (syn_cid) (.cv x)) (.cv x)) (.classMem (syn_cop (.cv x) (.cv x)) (syn_cid)) p0012 p0013
  have p0015 :=
    @g_mp2an (syn_wfn (syn_cid) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (.classEq (syn_cfv (syn_cid) (.cv x)) (.cv x)) p0006 p0007 p0014
  have p0016 :=
    @g_vtoclg (.classEq (syn_cfv (syn_cid) (.cv x)) (.cv x)) (.classEq (syn_cfv (syn_cid) A) A) x A V dv_cache_0001 dv_cache_0002 p0002 p0015
  exact p0016

noncomputable def g_fvresi
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (.classEq (syn_cfv (syn_cres (syn_cid) A) B) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_fvres B A (syn_cid)
  have p0001 :=
    @g_fvi B A
  have p0002 :=
    @g_eqtrd (.classMem B A) (syn_cfv (syn_cres (syn_cid) A) B) (syn_cfv (syn_cid) B) B p0000 p0001
  exact p0002

noncomputable def g_fvunsn
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wne B D) (.classEq (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D) (syn_cfv A D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_resundir A (syn_csn (syn_cop B C)) (syn_csn D)
  have p0001 :=
    @g_elsni B D
  have p0002 :=
    @g_necon3ai (.classMem B (syn_csn D)) B D p0001
  have p0003 :=
    @g_ressnop0 B C (syn_csn D)
  have p0004 :=
    @g_syl (syn_wne B D) (.neg (.classMem B (syn_csn D))) (.classEq (syn_cres (syn_csn (syn_cop B C)) (syn_csn D)) (syn_c0)) p0002 p0003
  have p0005 :=
    @g_uneq2d (syn_wne B D) (syn_cres (syn_csn (syn_cop B C)) (syn_csn D)) (syn_c0) (syn_cres A (syn_csn D)) p0004
  have p0006 :=
    @g_un0 (syn_cres A (syn_csn D))
  have p0007 :=
    @g_syl6eq (syn_wne B D) (syn_cun (syn_cres A (syn_csn D)) (syn_cres (syn_csn (syn_cop B C)) (syn_csn D))) (syn_cun (syn_cres A (syn_csn D)) (syn_c0)) (syn_cres A (syn_csn D)) p0005 p0006
  have p0008 :=
    @g_syl5eq (syn_wne B D) (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) (syn_cun (syn_cres A (syn_csn D)) (syn_cres (syn_csn (syn_cop B C)) (syn_csn D))) (syn_cres A (syn_csn D)) p0000 p0007
  have p0009 :=
    @g_fveq1d (syn_wne B D) D (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) (syn_cres A (syn_csn D)) p0008
  have p0010 :=
    @g_snidg D (syn_cvv)
  have p0011 :=
    @g_fvres D (syn_csn D) (syn_cun A (syn_csn (syn_cop B C)))
  have p0012 :=
    @g_syl (.classMem D (syn_cvv)) (.classMem D (syn_csn D)) (.classEq (syn_cfv (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) D) (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D)) p0010 p0011
  have p0013 :=
    @g_fvprc D (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D))
  have p0014 :=
    @g_fvprc D (syn_cun A (syn_csn (syn_cop B C)))
  have p0015 :=
    @g_eqtr4d (.neg (.classMem D (syn_cvv))) (syn_cfv (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) D) (syn_c0) (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D) p0013 p0014
  have p0016 :=
    @g_pm2_61i (.classMem D (syn_cvv)) (.classEq (syn_cfv (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) D) (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D)) p0012 p0015
  have p0017 :=
    @g_fvres D (syn_csn D) A
  have p0018 :=
    @g_syl (.classMem D (syn_cvv)) (.classMem D (syn_csn D)) (.classEq (syn_cfv (syn_cres A (syn_csn D)) D) (syn_cfv A D)) p0010 p0017
  have p0019 :=
    @g_fvprc D (syn_cres A (syn_csn D))
  have p0020 :=
    @g_fvprc D A
  have p0021 :=
    @g_eqtr4d (.neg (.classMem D (syn_cvv))) (syn_cfv (syn_cres A (syn_csn D)) D) (syn_c0) (syn_cfv A D) p0019 p0020
  have p0022 :=
    @g_pm2_61i (.classMem D (syn_cvv)) (.classEq (syn_cfv (syn_cres A (syn_csn D)) D) (syn_cfv A D)) p0018 p0021
  have p0023 :=
    @g_n_3eqtr3g (syn_wne B D) (syn_cfv (syn_cres (syn_cun A (syn_csn (syn_cop B C))) (syn_csn D)) D) (syn_cfv (syn_cres A (syn_csn D)) D) (syn_cfv (syn_cun A (syn_csn (syn_cop B C))) D) (syn_cfv A D) p0009 p0016 p0022
  exact p0023

noncomputable def g_fvconst2g
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem B D) (.classMem C A)) (.classEq (syn_cfv (syn_cxp A (syn_csn B)) C) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_fconstg A B D
  have p0001 :=
    @g_fvconst A B C (syn_cxp A (syn_csn B))
  have p0002 :=
    @g_sylan (.classMem B D) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) (.classMem C A) (.classEq (syn_cfv (syn_cxp A (syn_csn B)) C) B) p0000 p0001
  exact p0002

noncomputable def g_fvconst2
    (A : Class) (B : Class) (C : Class) (hyp_fvconst2_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem C A) (.classEq (syn_cfv (syn_cxp A (syn_csn B)) C) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_fvconst2g A B C (syn_cvv)
  have p0001 :=
    @g_mpan (.classMem B (syn_cvv)) (.classMem C A) (.classEq (syn_cfv (syn_cxp A (syn_csn B)) C) B) hyp_fvconst2_1 p0000
  exact p0001

noncomputable def g_funfvima
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem B (syn_cdm F))) (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_dmres F A
  have p0001 :=
    @g_eleq2i (syn_cdm (syn_cres F A)) (syn_cin A (syn_cdm F)) B p0000
  have p0002 :=
    @g_elin B A (syn_cdm F)
  have p0003 :=
    @g_bitri (.classMem B (syn_cdm (syn_cres F A))) (.classMem B (syn_cin A (syn_cdm F))) (syn_wa (.classMem B A) (.classMem B (syn_cdm F))) p0001 p0002
  have p0004 :=
    @g_funres A F
  have p0005 :=
    @g_fvelrn B (syn_cres F A)
  have p0006 :=
    @g_sylan (syn_wfun F) (syn_wfun (syn_cres F A)) (.classMem B (syn_cdm (syn_cres F A))) (.classMem (syn_cfv (syn_cres F A) B) (syn_crn (syn_cres F A))) p0004 p0005
  have p0007 :=
    @g_fvres B A F
  have p0008 :=
    @g_eleq1d (.classMem B A) (syn_cfv (syn_cres F A) B) (syn_cfv F B) (syn_crn (syn_cres F A)) p0007
  have p0009 :=
    @g_dfima3 F A
  have p0010 :=
    @g_eleq2i (syn_cima F A) (syn_crn (syn_cres F A)) (syn_cfv F B) p0009
  have p0011 :=
    @g_syl6rbbr (.classMem B A) (.classMem (syn_cfv (syn_cres F A) B) (syn_crn (syn_cres F A))) (.classMem (syn_cfv F B) (syn_crn (syn_cres F A))) (.classMem (syn_cfv F B) (syn_cima F A)) p0008 p0010
  have p0012 :=
    @g_syl5ibrcom (syn_wa (syn_wfun F) (.classMem B (syn_cdm (syn_cres F A)))) (.classMem (syn_cfv F B) (syn_cima F A)) (.classMem B A) (.classMem (syn_cfv (syn_cres F A) B) (syn_crn (syn_cres F A))) p0006 p0011
  have p0013 :=
    @g_ex (syn_wfun F) (.classMem B (syn_cdm (syn_cres F A))) (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A))) p0012
  have p0014 :=
    @g_syl5bir (syn_wa (.classMem B A) (.classMem B (syn_cdm F))) (.classMem B (syn_cdm (syn_cres F A))) (syn_wfun F) (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A))) p0003 p0013
  have p0015 :=
    @g_exp3a (syn_wfun F) (.classMem B A) (.classMem B (syn_cdm F)) (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A))) p0014
  have p0016 :=
    @g_com12 (syn_wfun F) (.classMem B A) (.imp (.classMem B (syn_cdm F)) (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A)))) p0015
  have p0017 :=
    @g_imp3a (.classMem B A) (syn_wfun F) (.classMem B (syn_cdm F)) (.imp (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A))) p0016
  have p0018 :=
    @g_pm2_43b (syn_wa (syn_wfun F) (.classMem B (syn_cdm F))) (.classMem B A) (.classMem (syn_cfv F B) (syn_cima F A)) p0017
  exact p0018

noncomputable def g_fniunfv
    (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wfn F A) (.classEq (syn_ciun x A (syn_cfv F (.cv x))) (syn_cuni (syn_crn F)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : y ∉ ((syn_cfv F (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fnrnfv x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_unieqd (syn_wfn F A) (syn_crn F) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0000
  have p0002 :=
    @g_fvex (.cv x) F
  have p0003 :=
    @g_dfiun2 x y A (syn_cfv F (.cv x)) dv_cache_0002 dv_cache_0006 dv_cache_0005 p0002
  have p0004 :=
    @g_syl6reqr (syn_wfn F A) (syn_cuni (syn_crn F)) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))))) (syn_ciun x A (syn_cfv F (.cv x))) p0001 p0003
  exact p0004

noncomputable def g_funiunfv
    (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wfun F) (.classEq (syn_ciun x A (syn_cfv F (.cv x))) (syn_cuni (syn_cima F A)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_F : w ∉ F.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cfv F (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cfv F (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cfv F (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_A_x, fresh_x_ne_z, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_wa (syn_wfun F) (.objMem w z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_w, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_cima F A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : w ∉ ((syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_z, fresh_w_ne_y, fresh_w_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ ((syn_cuni (syn_cima F A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_F, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fveq2 (.cv y) (.cv x) F
  have p0001 :=
    @g_eqid (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))
  have p0002 :=
    @g_fvex (.cv x) F
  have p0003 :=
    @g_fvopab4 y z (.cv x) (syn_cfv F (.cv y)) (syn_cfv F (.cv x)) A (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0000 p0001 p0002
  have p0004 :=
    @g_iuneq2i x A (syn_cfv (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))) (.cv x)) (syn_cfv F (.cv x)) p0003
  have p0005 :=
    @g_fvex (.cv y) F
  have p0006 :=
    @g_fnopab2 y z A (syn_cfv F (.cv y)) (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))) dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 p0005 p0001
  have p0007 :=
    @g_fniunfv x A (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))) dv_cache_0009 dv_cache_0010
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_eqtr3i (syn_ciun x A (syn_cfv (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))) (.cv x))) (syn_ciun x A (syn_cfv F (.cv x))) (syn_cuni (syn_crn (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))))) p0004 p0008
  have p0010 :=
    @g_rnopab2 y z A (syn_cfv F (.cv y)) dv_cache_0008
  have p0011 :=
    @g_unieqi (syn_crn (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y)))))) (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))) p0010
  have p0012 :=
    @g_eqcom (.cv z) (syn_cfv F (.cv y))
  have p0013 :=
    @g_idd (syn_wa (syn_wfun F) (.objMem w z)) (.classEq (syn_cfv F (.cv y)) (.cv z))
  have p0014 :=
    @g_funbrfv (.cv y) (.cv z) F
  have p0015 :=
    @g_adantr (syn_wfun F) (.imp (syn_wbr (.cv y) F (.cv z)) (.classEq (syn_cfv F (.cv y)) (.cv z))) (.objMem w z) p0014
  have p0016 :=
    @g_n0i (.cv z) (.cv w)
  have p0017 :=
    @g_ndmfv (.cv y) F
  have p0018 :=
    @g_eqeq1 (syn_cfv F (.cv y)) (.cv z) (syn_c0)
  have p0019 :=
    @g_syl5ib (.neg (.classMem (.cv y) (syn_cdm F))) (.classEq (syn_cfv F (.cv y)) (syn_c0)) (.classEq (syn_cfv F (.cv y)) (.cv z)) (.classEq (.cv z) (syn_c0)) p0017 p0018
  have p0020 :=
    @g_con1d (.classEq (syn_cfv F (.cv y)) (.cv z)) (.classMem (.cv y) (syn_cdm F)) (.classEq (.cv z) (syn_c0)) p0019
  have p0021_e00_recanon : Nominal.NPrf (.imp (.objMem w z) (.neg (.classEq (.cv z) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0021 :=
    @g_mpan9 (.objMem w z) (.neg (.classEq (.cv z) (syn_c0))) (.classEq (syn_cfv F (.cv y)) (.cv z)) (.classMem (.cv y) (syn_cdm F)) p0021_e00_recanon p0020
  have p0022 :=
    @g_funbrfvb (.cv y) (.cv z) F
  have p0023 :=
    @g_sylan2 (syn_wa (.objMem w z) (.classEq (syn_cfv F (.cv y)) (.cv z))) (syn_wfun F) (.classMem (.cv y) (syn_cdm F)) (syn_wb (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wbr (.cv y) F (.cv z))) p0021 p0022
  have p0024 :=
    @g_expr (syn_wfun F) (.objMem w z) (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wb (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wbr (.cv y) F (.cv z))) p0023
  have p0025 :=
    @g_pm5_21ndd (syn_wa (syn_wfun F) (.objMem w z)) (.classEq (syn_cfv F (.cv y)) (.cv z)) (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wbr (.cv y) F (.cv z)) p0013 p0015 p0024
  have p0026 :=
    @g_syl5bb (.classEq (.cv z) (syn_cfv F (.cv y))) (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wa (syn_wfun F) (.objMem w z)) (syn_wbr (.cv y) F (.cv z)) p0012 p0025
  have p0027 :=
    @g_rexbidv (syn_wa (syn_wfun F) (.objMem w z)) (.classEq (.cv z) (syn_cfv F (.cv y))) (syn_wbr (.cv y) F (.cv z)) y A dv_cache_0011 p0026
  have p0028 :=
    @g_pm5_32da (syn_wfun F) (.objMem w z) (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y)))) (syn_wrex y A (syn_wbr (.cv y) F (.cv z))) p0027
  have p0029 :=
    @g_exbidv (syn_wfun F) (syn_wa (.objMem w z) (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))) (syn_wa (.objMem w z) (syn_wrex y A (syn_wbr (.cv y) F (.cv z)))) z dv_cache_0012 p0028
  have p0030 :=
    @g_eluniab (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y)))) z (.cv w) dv_cache_0013
  have p0031 :=
    @g_eluni z (.cv w) (syn_cima F A) dv_cache_0013 dv_cache_0014
  have p0032 :=
    @g_elima y (.cv z) F A dv_cache_0015 dv_cache_0016 dv_cache_0006
  have p0033 :=
    @g_anbi2i (.classMem (.cv z) (syn_cima F A)) (syn_wrex y A (syn_wbr (.cv y) F (.cv z))) (.objMem w z) p0032
  have p0034 :=
    @g_exbii (syn_wa (.objMem w z) (.classMem (.cv z) (syn_cima F A))) (syn_wa (.objMem w z) (syn_wrex y A (syn_wbr (.cv y) F (.cv z)))) z p0033
  have p0035_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv w) (syn_cuni (syn_cima F A))) (syn_wex z (syn_wa (.objMem w z) (.classMem (.cv z) (syn_cima F A))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_cima syn_wrex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0031
  have p0035 :=
    @g_bitri (.classMem (.cv w) (syn_cuni (syn_cima F A))) (syn_wex z (syn_wa (.objMem w z) (.classMem (.cv z) (syn_cima F A)))) (syn_wex z (syn_wa (.objMem w z) (syn_wrex y A (syn_wbr (.cv y) F (.cv z))))) p0035_e00_recanon p0034
  have p0036_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv w) (syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))) (syn_wex z (syn_wa (.objMem w z) (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_wrex syn_cfv syn_cio syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0030
  have p0036 :=
    @g_n_3bitr4g (syn_wfun F) (syn_wex z (syn_wa (.objMem w z) (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y)))))) (syn_wex z (syn_wa (.objMem w z) (syn_wrex y A (syn_wbr (.cv y) F (.cv z))))) (.classMem (.cv w) (syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y))))))) (.classMem (.cv w) (syn_cuni (syn_cima F A))) p0029 p0036_e01_recanon p0035
  have p0037 :=
    @g_eqrdv (syn_wfun F) w (syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y)))))) (syn_cuni (syn_cima F A)) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0036
  have p0038 :=
    @g_syl5eq (syn_wfun F) (syn_cuni (syn_crn (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))))) (syn_cuni (.cab z (syn_wrex y A (.classEq (.cv z) (syn_cfv F (.cv y)))))) (syn_cuni (syn_cima F A)) p0011 p0037
  have p0039 :=
    @g_syl5eq (syn_wfun F) (syn_ciun x A (syn_cfv F (.cv x))) (syn_cuni (syn_crn (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) (syn_cfv F (.cv y))))))) (syn_cuni (syn_cima F A)) p0009 p0038
  exact p0039

noncomputable def g_eluniima
    (x : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wb (.classMem B (syn_cuni (syn_cima F A))) (syn_wrex x A (.classMem B (syn_cfv F (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eliun x B A (syn_cfv F (.cv x)) dv_cache_0001
  have p0001 :=
    @g_funiunfv x A F dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_eleq2d (syn_wfun F) (syn_ciun x A (syn_cfv F (.cv x))) (syn_cuni (syn_cima F A)) B p0001
  have p0003 :=
    @g_syl5rbbr (syn_wrex x A (.classMem B (syn_cfv F (.cv x)))) (.classMem B (syn_ciun x A (syn_cfv F (.cv x)))) (syn_wfun F) (.classMem B (syn_cuni (syn_cima F A))) p0000 p0002
  exact p0003

noncomputable def g_elunirn
    (x : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wb (.classMem A (syn_cuni (syn_crn F))) (syn_wrex x (syn_cdm F) (.classMem A (syn_cfv F (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ F.fv
  have dv_cache_0001 : x ∉ ((syn_cdm F)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_imadmrn F
  have p0001 :=
    @g_unieqi (syn_cima F (syn_cdm F)) (syn_crn F) p0000
  have p0002 :=
    @g_eleq2i (syn_cuni (syn_cima F (syn_cdm F))) (syn_cuni (syn_crn F)) A p0001
  have p0003 :=
    @g_eluniima x (syn_cdm F) A F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_syl5bbr (.classMem A (syn_cuni (syn_crn F))) (.classMem A (syn_cuni (syn_cima F (syn_cdm F)))) (syn_wfun F) (syn_wrex x (syn_cdm F) (.classMem A (syn_cfv F (.cv x)))) p0002 p0003
  exact p0004

#print axioms g_elunirn

end NFChoice.DirectNominalPrf.WPPReplay
