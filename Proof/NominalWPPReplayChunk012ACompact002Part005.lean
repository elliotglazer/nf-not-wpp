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
import NominalWPPReplayChunk012ACompact002Part004

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

noncomputable def g_eqfnfvd
    (ph : Wff) (x : Var) (A : Class) (F : Class) (G : Class) (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) (dv_ph_x : x ∉ ph.fv) (hyp_eqfnfvd_1 : Nominal.NPrf (.imp ph (syn_wfn F A))) (hyp_eqfnfvd_2 : Nominal.NPrf (.imp ph (syn_wfn G A))) (hyp_eqfnfvd_3 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))) :
    Nominal.NPrf (.imp ph (.classEq F G)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ F.fv ∪ G.fv
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0004 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ralrimiva ph (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) x A dv_cache_0001 hyp_eqfnfvd_3
  have p0001 :=
    @g_eqfnfv x A F G dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_syl2anc ph (syn_wfn F A) (syn_wfn G A) (syn_wb (.classEq F G) (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))) hyp_eqfnfvd_1 hyp_eqfnfvd_2 p0001
  have p0003 :=
    @g_mpbird ph (.classEq F G) (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) p0000 p0002
  exact p0003

noncomputable def g_funfvop
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem (syn_cop A (syn_cfv F A)) F)) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_eqid (syn_cfv F A)
  have p0001 :=
    @g_funopfvb A (syn_cfv F A) F
  have p0002 :=
    @g_mpbii (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classEq (syn_cfv F A) (syn_cfv F A)) (.classMem (syn_cop A (syn_cfv F A)) F) p0000 p0001
  exact p0002

noncomputable def g_funfvbrb
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wb (.classMem A (syn_cdm F)) (syn_wbr A F (syn_cfv F A)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_funfvop A F
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A F (syn_cfv F A))))
  have p0002 :=
    @g_sylibr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem (syn_cop A (syn_cfv F A)) F) (syn_wbr A F (syn_cfv F A)) p0000 p0001
  have p0003 :=
    @g_breldm A (syn_cfv F A) F
  have p0004 :=
    @g_adantl (syn_wbr A F (syn_cfv F A)) (.classMem A (syn_cdm F)) (syn_wfun F) p0003
  have p0005 :=
    @g_impbida (syn_wfun F) (.classMem A (syn_cdm F)) (syn_wbr A F (syn_cfv F A)) p0002 p0004
  exact p0005

noncomputable def g_fvimacnvi
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B))) (.classMem (syn_cfv F A) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_snssi A (syn_cima (syn_ccnv F) B)
  have p0001 :=
    @g_funimass2 (syn_csn A) B F
  have p0002 :=
    @g_sylan2 (.classMem A (syn_cima (syn_ccnv F) B)) (syn_wfun F) (syn_wss (syn_csn A) (syn_cima (syn_ccnv F) B)) (syn_wss (syn_cima F (syn_csn A)) B) p0000 p0001
  have p0003 :=
    @g_fvex A F
  have p0004 :=
    @g_snss (syn_cfv F A) B p0003
  have p0005 :=
    @g_cnvimass F B
  have p0006 :=
    @g_sseli (syn_cima (syn_ccnv F) B) (syn_cdm F) A p0005
  have p0007 :=
    @g_funfn F
  have p0008 :=
    @g_fnsnfv (syn_cdm F) A F
  have p0009 :=
    @g_sylanb (syn_wfun F) (syn_wfn F (syn_cdm F)) (.classMem A (syn_cdm F)) (.classEq (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A))) p0007 p0008
  have p0010 :=
    @g_sylan2 (.classMem A (syn_cima (syn_ccnv F) B)) (syn_wfun F) (.classMem A (syn_cdm F)) (.classEq (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A))) p0006 p0009
  have p0011 :=
    @g_sseq1d (syn_wa (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B))) (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A)) B p0010
  have p0012 :=
    @g_syl5bb (.classMem (syn_cfv F A) B) (syn_wss (syn_csn (syn_cfv F A)) B) (syn_wa (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B))) (syn_wss (syn_cima F (syn_csn A)) B) p0004 p0011
  have p0013 :=
    @g_mpbird (syn_wa (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B))) (.classMem (syn_cfv F A) B) (syn_wss (syn_cima F (syn_csn A)) B) p0002 p0012
  exact p0013

noncomputable def g_fvimacnv
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (syn_wb (.classMem (syn_cfv F A) B) (.classMem A (syn_cima (syn_ccnv F) B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_funfvop A F
  have p0001 :=
    @g_opelcnv (syn_cfv F A) A F
  have p0002 :=
    @g_sylibr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem (syn_cop A (syn_cfv F A)) F) (.classMem (syn_cop (syn_cfv F A) A) (syn_ccnv F)) p0000 p0001
  have p0003 :=
    @g_elimasn (syn_ccnv F) (syn_cfv F A) A
  have p0004 :=
    @g_sylibr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem (syn_cop (syn_cfv F A) A) (syn_ccnv F)) (.classMem A (syn_cima (syn_ccnv F) (syn_csn (syn_cfv F A)))) p0002 p0003
  have p0005 :=
    @g_fvex A F
  have p0006 :=
    @g_snss (syn_cfv F A) B p0005
  have p0007 :=
    @g_imass2 (syn_csn (syn_cfv F A)) B (syn_ccnv F)
  have p0008 :=
    @g_sylbi (.classMem (syn_cfv F A) B) (syn_wss (syn_csn (syn_cfv F A)) B) (syn_wss (syn_cima (syn_ccnv F) (syn_csn (syn_cfv F A))) (syn_cima (syn_ccnv F) B)) p0006 p0007
  have p0009 :=
    @g_sseld (.classMem (syn_cfv F A) B) (syn_cima (syn_ccnv F) (syn_csn (syn_cfv F A))) (syn_cima (syn_ccnv F) B) A p0008
  have p0010 :=
    @g_syl5com (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem A (syn_cima (syn_ccnv F) (syn_csn (syn_cfv F A)))) (.classMem (syn_cfv F A) B) (.classMem A (syn_cima (syn_ccnv F) B)) p0004 p0009
  have p0011 :=
    @g_fvimacnvi A B F
  have p0012 :=
    @g_ex (syn_wfun F) (.classMem A (syn_cima (syn_ccnv F) B)) (.classMem (syn_cfv F A) B) p0011
  have p0013 :=
    @g_adantr (syn_wfun F) (.imp (.classMem A (syn_cima (syn_ccnv F) B)) (.classMem (syn_cfv F A) B)) (.classMem A (syn_cdm F)) p0012
  have p0014 :=
    @g_impbid (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem (syn_cfv F A) B) (.classMem A (syn_cima (syn_ccnv F) B)) p0010 p0013
  exact p0014

noncomputable def g_funimass3
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wb (syn_wss (syn_cima F A) B) (syn_wss A (syn_cima (syn_ccnv F) B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cima (syn_ccnv F) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_funimass4 x A B F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_ssel A (syn_cdm F) (.cv x)
  have p0002 :=
    @g_fvimacnv (.cv x) B F
  have p0003 :=
    @g_ex (syn_wfun F) (.classMem (.cv x) (syn_cdm F)) (syn_wb (.classMem (syn_cfv F (.cv x)) B) (.classMem (.cv x) (syn_cima (syn_ccnv F) B))) p0002
  have p0004 :=
    @g_syl9r (syn_wss A (syn_cdm F)) (.classMem (.cv x) A) (.classMem (.cv x) (syn_cdm F)) (syn_wfun F) (syn_wb (.classMem (syn_cfv F (.cv x)) B) (.classMem (.cv x) (syn_cima (syn_ccnv F) B))) p0001 p0003
  have p0005 :=
    @g_imp31 (syn_wfun F) (syn_wss A (syn_cdm F)) (.classMem (.cv x) A) (syn_wb (.classMem (syn_cfv F (.cv x)) B) (.classMem (.cv x) (syn_cima (syn_ccnv F) B))) p0004
  have p0006 :=
    @g_ralbidva (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.classMem (syn_cfv F (.cv x)) B) (.classMem (.cv x) (syn_cima (syn_ccnv F) B)) x A dv_cache_0004 p0005
  have p0007 :=
    @g_bitrd (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wss (syn_cima F A) B) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) (syn_wral x A (.classMem (.cv x) (syn_cima (syn_ccnv F) B))) p0000 p0006
  have p0008 :=
    @g_dfss3 x A (syn_cima (syn_ccnv F) B) dv_cache_0001 dv_cache_0005
  have p0009 :=
    @g_syl6bbr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wss (syn_cima F A) B) (syn_wral x A (.classMem (.cv x) (syn_cima (syn_ccnv F) B))) (syn_wss A (syn_cima (syn_ccnv F) B)) p0007 p0008
  exact p0009

noncomputable def g_elpreima
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (syn_wb (.classMem B (syn_cima (syn_ccnv F) C)) (syn_wa (.classMem B A) (.classMem (syn_cfv F B) C)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_cnvimass F C
  have p0001 :=
    @g_sseli (syn_cima (syn_ccnv F) C) (syn_cdm F) B p0000
  have p0002 :=
    @g_fndm A F
  have p0003 :=
    @g_eleq2d (syn_wfn F A) (syn_cdm F) A B p0002
  have p0004 :=
    @g_syl5ib (.classMem B (syn_cima (syn_ccnv F) C)) (.classMem B (syn_cdm F)) (syn_wfn F A) (.classMem B A) p0001 p0003
  have p0005 :=
    @g_fnfun A F
  have p0006 :=
    @g_fvimacnvi B C F
  have p0007 :=
    @g_sylan (syn_wfn F A) (syn_wfun F) (.classMem B (syn_cima (syn_ccnv F) C)) (.classMem (syn_cfv F B) C) p0005 p0006
  have p0008 :=
    @g_ex (syn_wfn F A) (.classMem B (syn_cima (syn_ccnv F) C)) (.classMem (syn_cfv F B) C) p0007
  have p0009 :=
    @g_jcad (syn_wfn F A) (.classMem B (syn_cima (syn_ccnv F) C)) (.classMem B A) (.classMem (syn_cfv F B) C) p0004 p0008
  have p0010 :=
    @g_fvimacnv B C F
  have p0011 :=
    @g_funfni (syn_wb (.classMem (syn_cfv F B) C) (.classMem B (syn_cima (syn_ccnv F) C))) A B F p0010
  have p0012 :=
    @g_biimpd (syn_wa (syn_wfn F A) (.classMem B A)) (.classMem (syn_cfv F B) C) (.classMem B (syn_cima (syn_ccnv F) C)) p0011
  have p0013 :=
    @g_expimpd (syn_wfn F A) (.classMem B A) (.classMem (syn_cfv F B) C) (.classMem B (syn_cima (syn_ccnv F) C)) p0012
  have p0014 :=
    @g_impbid (syn_wfn F A) (.classMem B (syn_cima (syn_ccnv F) C)) (syn_wa (.classMem B A) (.classMem (syn_cfv F B) C)) p0009 p0013
  exact p0014

noncomputable def g_fimacnv
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (.classEq (syn_cima (syn_ccnv F) B) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_imassrn (syn_ccnv F) B
  have p0001 :=
    (by simpa [syn_cdm] using (Nominal.classEqRefl (syn_cdm F)))
  have p0002 :=
    @g_fdm A B F
  have p0003 :=
    @g_ssid A
  have p0004 :=
    @g_a1i (syn_wss A A) (syn_wf F A B) p0003
  have p0005 :=
    @g_eqsstrd (syn_wf F A B) (syn_cdm F) A A p0002 p0004
  have p0006 :=
    @g_syl5eqssr (syn_wf F A B) (syn_crn (syn_ccnv F)) (syn_cdm F) A p0001 p0005
  have p0007 :=
    @g_syl5ss (syn_wf F A B) (syn_cima (syn_ccnv F) B) (syn_crn (syn_ccnv F)) A p0000 p0006
  have p0008 :=
    @g_imassrn F A
  have p0009 :=
    @g_frn A B F
  have p0010 :=
    @g_syl5ss (syn_wf F A B) (syn_cima F A) (syn_crn F) B p0008 p0009
  have p0011 :=
    @g_ffun A B F
  have p0012 :=
    @g_syl5sseqr (syn_wf F A B) A A (syn_cdm F) p0003 p0002
  have p0013 :=
    @g_funimass3 A B F
  have p0014 :=
    @g_syl2anc (syn_wf F A B) (syn_wfun F) (syn_wss A (syn_cdm F)) (syn_wb (syn_wss (syn_cima F A) B) (syn_wss A (syn_cima (syn_ccnv F) B))) p0011 p0012 p0013
  have p0015 :=
    @g_mpbid (syn_wf F A B) (syn_wss (syn_cima F A) B) (syn_wss A (syn_cima (syn_ccnv F) B)) p0010 p0014
  have p0016 :=
    @g_eqssd (syn_wf F A B) (syn_cima (syn_ccnv F) B) A p0007 p0015
  exact p0016

noncomputable def g_fvelrn
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem (syn_cfv F A) (syn_crn F))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (syn_cop A (syn_cfv F A)) F)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cfv F A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wfun F) (.classMem A (syn_cdm F))
  have p0001 :=
    @g_funfvop A F
  have p0002 :=
    @g_opeq1 (.cv x) A (syn_cfv F A)
  have p0003 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cfv F A)) (syn_cop A (syn_cfv F A)) F p0002
  have p0004 :=
    @g_spcegv (.classMem (syn_cop (.cv x) (syn_cfv F A)) F) (.classMem (syn_cop A (syn_cfv F A)) F) x A (syn_cdm F) dv_cache_0001 dv_cache_0002 p0003
  have p0005 :=
    @g_sylc (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classMem A (syn_cdm F)) (.classMem (syn_cop A (syn_cfv F A)) F) (syn_wex x (.classMem (syn_cop (.cv x) (syn_cfv F A)) F)) p0000 p0001 p0004
  have p0006 :=
    @g_elrn2 x (syn_cfv F A) F dv_cache_0003 dv_cache_0004
  have p0007 :=
    @g_sylibr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (syn_wex x (.classMem (syn_cop (.cv x) (syn_cfv F A)) F)) (.classMem (syn_cfv F A) (syn_crn F)) p0005 p0006
  exact p0007

noncomputable def g_fnfvelrn
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem B A)) (.classMem (syn_cfv F B) (syn_crn F))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fvelrn B F
  have p0001 :=
    @g_funfni (.classMem (syn_cfv F B) (syn_crn F)) A B F p0000
  exact p0001

noncomputable def g_ffvelrn
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf F A B) (.classMem C A)) (.classMem (syn_cfv F C) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_ffn A B F
  have p0001 :=
    @g_fnfvelrn A C F
  have p0002 :=
    @g_sylan (syn_wf F A B) (syn_wfn F A) (.classMem C A) (.classMem (syn_cfv F C) (syn_crn F)) p0000 p0001
  have p0003 :=
    @g_frn A B F
  have p0004 :=
    @g_sseld (syn_wf F A B) (syn_crn F) B (syn_cfv F C) p0003
  have p0005 :=
    @g_adantr (syn_wf F A B) (.imp (.classMem (syn_cfv F C) (syn_crn F)) (.classMem (syn_cfv F C) B)) (.classMem C A) p0004
  have p0006 :=
    @g_mpd (syn_wa (syn_wf F A B) (.classMem C A)) (.classMem (syn_cfv F C) (syn_crn F)) (.classMem (syn_cfv F C) B) p0002 p0005
  exact p0006

noncomputable def g_ffvelrni
    (A : Class) (B : Class) (C : Class) (F : Class) (hyp_ffvrni_1 : Nominal.NPrf (syn_wf F A B)) :
    Nominal.NPrf (.imp (.classMem C A) (.classMem (syn_cfv F C) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_ffvelrn A B C F
  have p0001 :=
    @g_mpan (syn_wf F A B) (.classMem C A) (.classMem (syn_cfv F C) B) hyp_ffvrni_1 p0000
  exact p0001

noncomputable def g_dffo3
    (x : Var) (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wfo F A B) (syn_wa (syn_wf F A B) (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0006 : x ∉ ((Wff.classMem (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wf F A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wf F A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dffo2 A B F
  have p0001 :=
    @g_ffn A B F
  have p0002 :=
    @g_fnrnfv x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0003 :=
    @g_eqeq1d (syn_wfn F A) (syn_crn F) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B p0002
  have p0004 :=
    @g_syl (syn_wf F A B) (syn_wfn F A) (syn_wb (.classEq (syn_crn F) B) (.classEq (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B)) p0001 p0003
  have p0005 :=
    @g_simpr (syn_wa (syn_wf F A B) (.classMem (.cv x) A)) (.classEq (.cv y) (syn_cfv F (.cv x)))
  have p0006 :=
    @g_ffvelrn A B (.cv x) F
  have p0007 :=
    @g_adantr (syn_wa (syn_wf F A B) (.classMem (.cv x) A)) (.classMem (syn_cfv F (.cv x)) B) (.classEq (.cv y) (syn_cfv F (.cv x))) p0006
  have p0008 :=
    @g_eqeltrd (syn_wa (syn_wa (syn_wf F A B) (.classMem (.cv x) A)) (.classEq (.cv y) (syn_cfv F (.cv x)))) (.cv y) (syn_cfv F (.cv x)) B p0005 p0007
  have p0009 :=
    @g_exp31 (syn_wf F A B) (.classMem (.cv x) A) (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B) p0008
  have p0010 :=
    @g_rexlimdv (syn_wf F A B) (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B) x A dv_cache_0006 dv_cache_0007 p0009
  have p0011 :=
    @g_biantrurd (syn_wf F A B) (.imp (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B)) (.imp (.classMem (.cv y) B) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0010
  have p0012 :=
    @g_dfbi2 (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B)
  have p0013 :=
    @g_syl6rbbr (syn_wf F A B) (.imp (.classMem (.cv y) B) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) (syn_wa (.imp (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B)) (.imp (.classMem (.cv y) B) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))))) (syn_wb (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B)) p0011 p0012
  have p0014 :=
    @g_albidv (syn_wf F A B) (syn_wb (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B)) (.imp (.classMem (.cv y) B) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) y dv_cache_0008 p0013
  have p0015 :=
    @g_eqabcb (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) y B dv_cache_0009
  have p0016 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))))))
  have p0017 :=
    @g_n_3bitr4g (syn_wf F A B) (.all y (syn_wb (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B))) (.all y (.imp (.classMem (.cv y) B) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))))) (.classEq (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B) (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0014 p0015 p0016
  have p0018 :=
    @g_bitrd (syn_wf F A B) (.classEq (syn_crn F) B) (.classEq (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B) (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0004 p0017
  have p0019 :=
    @g_pm5_32i (syn_wf F A B) (.classEq (syn_crn F) B) (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0018
  have p0020 :=
    @g_bitri (syn_wfo F A B) (syn_wa (syn_wf F A B) (.classEq (syn_crn F) B)) (syn_wa (syn_wf F A B) (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))))) p0000 p0019
  exact p0020

noncomputable def g_foelrn
    (x : Var) (A : Class) (B : Class) (C : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfo F A B) (.classMem C B)) (syn_wrex x A (.classEq C (syn_cfv F (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
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
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ ((Wff.classEq (.cv y) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_wrex x A (.classEq C (syn_cfv F (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_C, fresh_y_ne_x, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dffo3 x y A B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_simprbi (syn_wfo F A B) (syn_wf F A B) (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0000
  have p0002 :=
    @g_eqeq1 (.cv y) C (syn_cfv F (.cv x))
  have p0003 :=
    @g_rexbidv (.classEq (.cv y) C) (.classEq (.cv y) (syn_cfv F (.cv x))) (.classEq C (syn_cfv F (.cv x))) x A dv_cache_0008 p0002
  have p0004 :=
    @g_rspccva (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (syn_wrex x A (.classEq C (syn_cfv F (.cv x)))) y C B dv_cache_0009 dv_cache_0004 dv_cache_0010 p0003
  have p0005 :=
    @g_sylan (syn_wfo F A B) (syn_wral y B (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) (.classMem C B) (syn_wrex x A (.classEq C (syn_cfv F (.cv x)))) p0001 p0004
  exact p0005

noncomputable def g_ffnfv
    (x : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (syn_wb (syn_wf F A B) (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_wf F A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_crn F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, fresh_y_ne_x, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ffn A B F
  have p0001 :=
    @g_ffvelrn A B (.cv x) F
  have p0002 :=
    @g_ralrimiva (syn_wf F A B) (.classMem (syn_cfv F (.cv x)) B) x A dv_cache_0001 p0001
  have p0003 :=
    @g_jca (syn_wf F A B) (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) p0000 p0002
  have p0004 :=
    @g_simpl (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))
  have p0005 :=
    @g_fvelrnb x A (.cv y) F dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_biimpd (syn_wfn F A) (.classMem (.cv y) (syn_crn F)) (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y))) p0005
  have p0007 :=
    @g_nfra1 (.classMem (syn_cfv F (.cv x)) B) x A
  have p0008 :=
    @g_nfv (.classMem (.cv y) B) x dv_cache_0005
  have p0009 :=
    @g_rsp (.classMem (syn_cfv F (.cv x)) B) x A
  have p0010 :=
    @g_eleq1 (syn_cfv F (.cv x)) (.cv y) B
  have p0011 :=
    @g_biimpcd (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (syn_cfv F (.cv x)) B) (.classMem (.cv y) B) p0010
  have p0012 :=
    @g_syl6 (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) (.classMem (.cv x) A) (.classMem (syn_cfv F (.cv x)) B) (.imp (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (.cv y) B)) p0009 p0011
  have p0013 :=
    @g_rexlimd (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (.cv y) B) x A p0007 p0008 p0012
  have p0014 :=
    @g_sylan9 (syn_wfn F A) (.classMem (.cv y) (syn_crn F)) (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y))) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) (.classMem (.cv y) B) p0006 p0013
  have p0015 :=
    @g_ssrdv (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))) y (syn_crn F) B dv_cache_0006 dv_cache_0007 dv_cache_0008 p0014
  have p0016 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0017 :=
    @g_sylanbrc (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))) (syn_wfn F A) (syn_wss (syn_crn F) B) (syn_wf F A B) p0004 p0015 p0016
  have p0018 :=
    @g_impbii (syn_wf F A B) (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))) p0003 p0017
  exact p0018

noncomputable def g_fnfvrnss
    (x : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))) (syn_wss (syn_crn F) B)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ffnfv x A B F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_frn A B F
  have p0002 :=
    @g_sylbir (syn_wa (syn_wfn F A) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B))) (syn_wf F A B) (syn_wss (syn_crn F) B) p0000 p0001
  exact p0002

noncomputable def g_fsn
    (A : Class) (B : Class) (F : Class) (hyp_fsn_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fsn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wf F (syn_csn A) (syn_csn B)) (.classEq F (syn_csn (syn_cop A B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_csn A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_csn B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.classMem (syn_cop A B) F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_csn (syn_cop A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_csn (syn_cop A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_wf F (syn_csn A) (syn_csn B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_wf F (syn_csn A) (syn_csn B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_opelf (syn_csn A) (syn_csn B) (.cv x) (.cv y) F
  have p0001 :=
    @g_elsn x A dv_cache_0001
  have p0002 :=
    @g_elsn y B dv_cache_0002
  have p0003 :=
    @g_anbi12i (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A) (.classMem (.cv y) (syn_csn B)) (.classEq (.cv y) B) p0001 p0002
  have p0004 :=
    @g_sylib (syn_wa (syn_wf F (syn_csn A) (syn_csn B)) (.classMem (syn_cop (.cv x) (.cv y)) F)) (syn_wa (.classMem (.cv x) (syn_csn A)) (.classMem (.cv y) (syn_csn B))) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0000 p0003
  have p0005 :=
    @g_ex (syn_wf F (syn_csn A) (syn_csn B)) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0004
  have p0006 :=
    @g_snid A hyp_fsn_1
  have p0007 :=
    @g_feu y (syn_csn A) (syn_csn B) A F dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 :=
    @g_mpan2 (syn_wf F (syn_csn A) (syn_csn B)) (.classMem A (syn_csn A)) (syn_wreu y (syn_csn B) (.classMem (syn_cop A (.cv y)) F)) p0006 p0007
  have p0009 :=
    @g_anbi1i (.classMem (.cv y) (syn_csn B)) (.classEq (.cv y) B) (.classMem (syn_cop A (.cv y)) F) p0002
  have p0010 :=
    @g_opeq2 (.cv y) B A
  have p0011 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_cop A (.cv y)) (syn_cop A B) F p0010
  have p0012 :=
    @g_pm5_32i (.classEq (.cv y) B) (.classMem (syn_cop A (.cv y)) F) (.classMem (syn_cop A B) F) p0011
  have p0013 :=
    @g_ancom (.classMem (syn_cop A B) F) (.classEq (.cv y) B)
  have p0014 :=
    @g_bitr4i (syn_wa (.classEq (.cv y) B) (.classMem (syn_cop A (.cv y)) F)) (syn_wa (.classEq (.cv y) B) (.classMem (syn_cop A B) F)) (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B)) p0012 p0013
  have p0015 :=
    @g_bitr2i (syn_wa (.classMem (.cv y) (syn_csn B)) (.classMem (syn_cop A (.cv y)) F)) (syn_wa (.classEq (.cv y) B) (.classMem (syn_cop A (.cv y)) F)) (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B)) p0009 p0014
  have p0016 :=
    @g_eubii (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B)) (syn_wa (.classMem (.cv y) (syn_csn B)) (.classMem (syn_cop A (.cv y)) F)) y p0015
  have p0017 :=
    @g_eueq1 y B dv_cache_0002 hyp_fsn_2
  have p0018 :=
    @g_biantru (syn_weu y (.classEq (.cv y) B)) (.classMem (syn_cop A B) F) p0017
  have p0019 :=
    @g_euanv (.classMem (syn_cop A B) F) (.classEq (.cv y) B) y dv_cache_0007
  have p0020 :=
    @g_bitr4i (.classMem (syn_cop A B) F) (syn_wa (.classMem (syn_cop A B) F) (syn_weu y (.classEq (.cv y) B))) (syn_weu y (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B))) p0018 p0019
  have p0021 :=
    (by simpa [syn_wb, syn_wreu] using (Nominal.biimpRefl (syn_wreu y (syn_csn B) (.classMem (syn_cop A (.cv y)) F))))
  have p0022 :=
    @g_n_3bitr4i (syn_weu y (syn_wa (.classMem (syn_cop A B) F) (.classEq (.cv y) B))) (syn_weu y (syn_wa (.classMem (.cv y) (syn_csn B)) (.classMem (syn_cop A (.cv y)) F))) (.classMem (syn_cop A B) F) (syn_wreu y (syn_csn B) (.classMem (syn_cop A (.cv y)) F)) p0016 p0020 p0021
  have p0023 :=
    @g_sylibr (syn_wf F (syn_csn A) (syn_csn B)) (syn_wreu y (syn_csn B) (.classMem (syn_cop A (.cv y)) F)) (.classMem (syn_cop A B) F) p0008 p0022
  have p0024 :=
    @g_opeq12 (.cv x) A (.cv y) B
  have p0025 :=
    @g_eleq1d (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_cop (.cv x) (.cv y)) (syn_cop A B) F p0024
  have p0026 :=
    @g_syl5ibrcom (syn_wf F (syn_csn A) (syn_csn B)) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classMem (syn_cop A B) F) p0023 p0025
  have p0027 :=
    @g_impbid (syn_wf F (syn_csn A) (syn_csn B)) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0005 p0026
  have p0028 :=
    @g_vex x
  have p0029 :=
    @g_vex y
  have p0030 :=
    @g_opex (.cv x) (.cv y) p0028 p0029
  have p0031 :=
    @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop A B) p0030
  have p0032 :=
    @g_opth (.cv x) (.cv y) A B
  have p0033 :=
    @g_bitr2i (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B)) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0031 p0032
  have p0034 :=
    @g_syl6bb (syn_wf F (syn_csn A) (syn_csn B)) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B))) p0027 p0033
  have p0035 :=
    @g_eqrelrdv (syn_wf F (syn_csn A) (syn_csn B)) x y F (syn_csn (syn_cop A B)) dv_cache_0008 dv_cache_0006 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 p0034
  have p0036 :=
    @g_f1osn A B hyp_fsn_1 hyp_fsn_2
  have p0037 :=
    @g_f1oeq1 (syn_csn A) (syn_csn B) F (syn_csn (syn_cop A B))
  have p0038 :=
    @g_mpbiri (.classEq F (syn_csn (syn_cop A B))) (syn_wf1o F (syn_csn A) (syn_csn B)) (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) p0036 p0037
  have p0039 :=
    @g_f1of (syn_csn A) (syn_csn B) F
  have p0040 :=
    @g_syl (.classEq F (syn_csn (syn_cop A B))) (syn_wf1o F (syn_csn A) (syn_csn B)) (syn_wf F (syn_csn A) (syn_csn B)) p0038 p0039
  have p0041 :=
    @g_impbii (syn_wf F (syn_csn A) (syn_csn B)) (.classEq F (syn_csn (syn_cop A B))) p0035 p0040
  exact p0041

#print axioms g_fsn

end NFChoice.DirectNominalPrf.WPPReplay
