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
import NominalWPPReplayChunk011Compact001

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

noncomputable def g_f1oeq3
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf1o F C A) (syn_wf1o F C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_f1eq3 A B C F
  have p0001 :=
    @g_foeq3 A B C F
  have p0002 :=
    @g_anbi12d (.classEq A B) (syn_wf1 F C A) (syn_wf1 F C B) (syn_wfo F C A) (syn_wfo F C B) p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F C A)))
  have p0004 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F C B)))
  have p0005 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wf1 F C A) (syn_wfo F C A)) (syn_wa (syn_wf1 F C B) (syn_wfo F C B)) (syn_wf1o F C A) (syn_wf1o F C B) p0002 p0003 p0004
  exact p0005

noncomputable def g_f1oeq23
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq A B) (.classEq C D)) (syn_wb (syn_wf1o F A C) (syn_wf1o F B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  have p0000 :=
    @g_f1oeq2 A B C F
  have p0001 :=
    @g_f1oeq3 C D B F
  have p0002 :=
    @g_sylan9bb (.classEq A B) (syn_wf1o F A C) (syn_wf1o F B C) (.classEq C D) (syn_wf1o F B D) p0000 p0001
  exact p0002

noncomputable def g_f1of1
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wf1 F A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F A B)))
  have p0001 :=
    @g_simplbi (syn_wf1o F A B) (syn_wf1 F A B) (syn_wfo F A B) p0000
  exact p0001

noncomputable def g_f1of
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wf F A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1of1 A B F
  have p0001 :=
    @g_f1f A B F
  have p0002 :=
    @g_syl (syn_wf1o F A B) (syn_wf1 F A B) (syn_wf F A B) p0000 p0001
  exact p0002

noncomputable def g_f1ofn
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wfn F A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1of A B F
  have p0001 :=
    @g_ffn A B F
  have p0002 :=
    @g_syl (syn_wf1o F A B) (syn_wf F A B) (syn_wfn F A) p0000 p0001
  exact p0002

noncomputable def g_f1ofun
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wfun F)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1ofn A B F
  have p0001 :=
    @g_fnfun A F
  have p0002 :=
    @g_syl (syn_wf1o F A B) (syn_wfn F A) (syn_wfun F) p0000 p0001
  exact p0002

noncomputable def g_f1odm
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (.classEq (syn_cdm F) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1ofn A B F
  have p0001 :=
    @g_fndm A F
  have p0002 :=
    @g_syl (syn_wf1o F A B) (syn_wfn F A) (.classEq (syn_cdm F) A) p0000 p0001
  exact p0002

noncomputable def g_dff1o2
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wf1o F A B) (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F A B)))
  have p0001 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A B)))
  have p0002 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F A B)))
  have p0003 :=
    @g_anbi12i (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))) (syn_wfo F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) p0001 p0002
  have p0004 :=
    @g_ancom (syn_wf F A B) (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
  have p0005 :=
    @g_n_3anass (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)
  have p0006 :=
    @g_an12 (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)
  have p0007 :=
    @g_bitri (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wa (syn_wfn F A) (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))) (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))) p0005 p0006
  have p0008 :=
    @g_anbi1i (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))) (syn_wf F A B) p0007
  have p0009 :=
    @g_bitr4i (syn_wa (syn_wf F A B) (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))) (syn_wa (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))) (syn_wf F A B)) (syn_wa (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wf F A B)) p0004 p0008
  have p0010 :=
    @g_anass (syn_wf F A B) (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))
  have p0011 :=
    @g_eqimss (syn_crn F) B
  have p0012 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0013 :=
    @g_biimpri (syn_wf F A B) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) p0012
  have p0014 :=
    @g_sylan2 (.classEq (syn_crn F) B) (syn_wfn F A) (syn_wss (syn_crn F) B) (syn_wf F A B) p0011 p0013
  have p0015 :=
    @g_n_3adant2 (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wf F A B) (syn_wfun (syn_ccnv F)) p0014
  have p0016 :=
    @g_pm4_71i (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wf F A B) p0015
  have p0017 :=
    @g_n_3bitr4i (syn_wa (syn_wf F A B) (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))) (syn_wa (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wf F A B)) (syn_wa (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))) (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) p0009 p0010 p0016
  have p0018 :=
    @g_n_3bitri (syn_wf1o F A B) (syn_wa (syn_wf1 F A B) (syn_wfo F A B)) (syn_wa (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))) (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) p0000 p0003 p0017
  exact p0018

noncomputable def g_dff1o3
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wf1o F A B) (syn_wa (syn_wfo F A B) (syn_wfun (syn_ccnv F)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))))
  have p0001 :=
    @g_an32 (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)
  have p0002 :=
    @g_bitri (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wa (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F))) (.classEq (syn_crn F) B)) (syn_wa (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wfun (syn_ccnv F))) p0000 p0001
  have p0003 :=
    @g_dff1o2 A B F
  have p0004 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F A B)))
  have p0005 :=
    @g_anbi1i (syn_wfo F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wfun (syn_ccnv F)) p0004
  have p0006 :=
    @g_n_3bitr4i (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wa (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wfun (syn_ccnv F))) (syn_wf1o F A B) (syn_wa (syn_wfo F A B) (syn_wfun (syn_ccnv F))) p0002 p0003 p0005
  exact p0006

noncomputable def g_f1ofo
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wfo F A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_dff1o3 A B F
  have p0001 :=
    @g_simplbi (syn_wf1o F A B) (syn_wfo F A B) (syn_wfun (syn_ccnv F)) p0000
  exact p0001

noncomputable def g_dff1o4
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wf1o F A B) (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_dff1o2 A B F
  have p0001 :=
    @g_n_3anass (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)
  have p0002 :=
    @g_dfrn4 F
  have p0003 :=
    @g_eqeq1i (syn_crn F) (syn_cdm (syn_ccnv F)) B p0002
  have p0004 :=
    @g_anbi2i (.classEq (syn_crn F) B) (.classEq (syn_cdm (syn_ccnv F)) B) (syn_wfun (syn_ccnv F)) p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_ccnv F) B)))
  have p0006 :=
    @g_bitr4i (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_cdm (syn_ccnv F)) B)) (syn_wfn (syn_ccnv F) B) p0004 p0005
  have p0007 :=
    @g_anbi2i (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wfn (syn_ccnv F) B) (syn_wfn F A) p0006
  have p0008 :=
    @g_n_3bitri (syn_wf1o F A B) (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) (syn_wa (syn_wfn F A) (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))) (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B)) p0000 p0001 p0007
  exact p0008

noncomputable def g_dff1o5
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wf1o F A B) (syn_wa (syn_wf1 F A B) (.classEq (syn_crn F) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F A B)))
  have p0001 :=
    @g_f1f A B F
  have p0002 :=
    @g_biantrurd (syn_wf1 F A B) (syn_wf F A B) (.classEq (syn_crn F) B) p0001
  have p0003 :=
    @g_dffo2 A B F
  have p0004 :=
    @g_syl6rbbr (syn_wf1 F A B) (.classEq (syn_crn F) B) (syn_wa (syn_wf F A B) (.classEq (syn_crn F) B)) (syn_wfo F A B) p0002 p0003
  have p0005 :=
    @g_pm5_32i (syn_wf1 F A B) (syn_wfo F A B) (.classEq (syn_crn F) B) p0004
  have p0006 :=
    @g_bitri (syn_wf1o F A B) (syn_wa (syn_wf1 F A B) (syn_wfo F A B)) (syn_wa (syn_wf1 F A B) (.classEq (syn_crn F) B)) p0000 p0005
  exact p0006

noncomputable def g_f1orn
    (A : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wf1o F A (syn_crn F)) (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) (syn_crn F)))))
  have p0001 :=
    @g_dff1o2 A (syn_crn F) F
  have p0002 :=
    @g_eqid (syn_crn F)
  have p0003 :=
    @g_biantru (.classEq (syn_crn F) (syn_crn F)) (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F))) p0002
  have p0004 :=
    @g_n_3bitr4i (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) (syn_crn F))) (syn_wa (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F))) (.classEq (syn_crn F) (syn_crn F))) (syn_wf1o F A (syn_crn F)) (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F))) p0000 p0001 p0003
  exact p0004

noncomputable def g_f1f1orn
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1 F A B) (syn_wf1o F A (syn_crn F))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1fn A B F
  have p0001 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A B)))
  have p0002 :=
    @g_simprbi (syn_wf1 F A B) (syn_wf F A B) (syn_wfun (syn_ccnv F)) p0001
  have p0003 :=
    @g_f1orn A F
  have p0004 :=
    @g_sylanbrc (syn_wf1 F A B) (syn_wfn F A) (syn_wfun (syn_ccnv F)) (syn_wf1o F A (syn_crn F)) p0000 p0002 p0003
  exact p0004

noncomputable def g_f1ocnvb
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_cnvcnv F
  have p0001 :=
    @g_fneq1i A (syn_ccnv (syn_ccnv F)) F p0000
  have p0002 :=
    @g_anbi2i (syn_wfn (syn_ccnv (syn_ccnv F)) A) (syn_wfn F A) (syn_wfn (syn_ccnv F) B) p0001
  have p0003 :=
    @g_ancom (syn_wfn (syn_ccnv F) B) (syn_wfn F A)
  have p0004 :=
    @g_bitri (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv (syn_ccnv F)) A)) (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn F A)) (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B)) p0002 p0003
  have p0005 :=
    @g_dff1o4 B A (syn_ccnv F)
  have p0006 :=
    @g_dff1o4 A B F
  have p0007 :=
    @g_n_3bitr4ri (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv (syn_ccnv F)) A)) (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B)) (syn_wf1o (syn_ccnv F) B A) (syn_wf1o F A B) p0004 p0005 p0006
  exact p0007

noncomputable def g_f1ocnv
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1ocnvb A B F
  have p0001 :=
    @g_biimpi (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A) p0000
  exact p0001

noncomputable def g_f1ores
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1 F A B) (syn_wss C A)) (syn_wf1o (syn_cres F C) C (syn_cima F C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_ffun A B F
  have p0001 :=
    @g_adantr (syn_wf F A B) (syn_wfun F) (syn_wss C A) p0000
  have p0002 :=
    @g_fdm A B F
  have p0003 :=
    @g_sseq2d (syn_wf F A B) (syn_cdm F) A C p0002
  have p0004 :=
    @g_biimpar (syn_wf F A B) (syn_wss C (syn_cdm F)) (syn_wss C A) p0003
  have p0005 :=
    @g_fores C F
  have p0006 :=
    @g_syl2anc (syn_wa (syn_wf F A B) (syn_wss C A)) (syn_wfun F) (syn_wss C (syn_cdm F)) (syn_wfo (syn_cres F C) C (syn_cima F C)) p0001 p0004 p0005
  have p0007 :=
    @g_funres11 C F
  have p0008 :=
    @g_anim12i (syn_wa (syn_wf F A B) (syn_wss C A)) (syn_wfo (syn_cres F C) C (syn_cima F C)) (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv (syn_cres F C))) p0006 p0007
  have p0009 :=
    @g_an32s (syn_wf F A B) (syn_wss C A) (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfo (syn_cres F C) C (syn_cima F C)) (syn_wfun (syn_ccnv (syn_cres F C)))) p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A B)))
  have p0011 :=
    @g_anbi1i (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))) (syn_wss C A) p0010
  have p0012 :=
    @g_dff1o3 C (syn_cima F C) (syn_cres F C)
  have p0013 :=
    @g_n_3imtr4i (syn_wa (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))) (syn_wss C A)) (syn_wa (syn_wfo (syn_cres F C) C (syn_cima F C)) (syn_wfun (syn_ccnv (syn_cres F C)))) (syn_wa (syn_wf1 F A B) (syn_wss C A)) (syn_wf1o (syn_cres F C) C (syn_cima F C)) p0009 p0011 p0012
  exact p0013

noncomputable def g_f1oun
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wf1o F A B) (syn_wf1o G C D)) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))) (syn_wf1o (syn_cun F G) (syn_cun A C) (syn_cun B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_dff1o4 A B F
  have p0001 :=
    @g_dff1o4 C D G
  have p0002 :=
    @g_fnun A C F G
  have p0003 :=
    @g_ex (syn_wa (syn_wfn F A) (syn_wfn G C)) (.classEq (syn_cin A C) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A C)) p0002
  have p0004 :=
    @g_fnun B D (syn_ccnv F) (syn_ccnv G)
  have p0005 :=
    @g_cnvun F G
  have p0006 :=
    @g_fneq1i (syn_cun B D) (syn_ccnv (syn_cun F G)) (syn_cun (syn_ccnv F) (syn_ccnv G)) p0005
  have p0007 :=
    @g_sylibr (syn_wa (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv G) D)) (.classEq (syn_cin B D) (syn_c0))) (syn_wfn (syn_cun (syn_ccnv F) (syn_ccnv G)) (syn_cun B D)) (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D)) p0004 p0006
  have p0008 :=
    @g_ex (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv G) D)) (.classEq (syn_cin B D) (syn_c0)) (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D)) p0007
  have p0009 :=
    @g_im2anan9 (syn_wa (syn_wfn F A) (syn_wfn G C)) (.classEq (syn_cin A C) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A C)) (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv G) D)) (.classEq (syn_cin B D) (syn_c0)) (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D)) p0003 p0008
  have p0010 :=
    @g_an4s (syn_wfn F A) (syn_wfn G C) (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv G) D) (.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) (syn_wa (syn_wfn (syn_cun F G) (syn_cun A C)) (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D)))) p0009
  have p0011 :=
    @g_syl2anb (syn_wf1o F A B) (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B)) (syn_wa (syn_wfn G C) (syn_wfn (syn_ccnv G) D)) (.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) (syn_wa (syn_wfn (syn_cun F G) (syn_cun A C)) (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D)))) (syn_wf1o G C D) p0000 p0001 p0010
  have p0012 :=
    @g_dff1o4 (syn_cun A C) (syn_cun B D) (syn_cun F G)
  have p0013 :=
    @g_syl6ibr (syn_wa (syn_wf1o F A B) (syn_wf1o G C D)) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) (syn_wa (syn_wfn (syn_cun F G) (syn_cun A C)) (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D))) (syn_wf1o (syn_cun F G) (syn_cun A C) (syn_cun B D)) p0011 p0012
  have p0014 :=
    @g_imp (syn_wa (syn_wf1o F A B) (syn_wf1o G C D)) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) (syn_wf1o (syn_cun F G) (syn_cun A C) (syn_cun B D)) p0013
  exact p0014

noncomputable def g_f1oco
    (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1o F B C) (syn_wf1o G A B)) (syn_wf1o (syn_ccom F G) A C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_f1co A B C F G
  have p0001 :=
    @g_foco A B C F G
  have p0002 :=
    @g_anim12i (syn_wa (syn_wf1 F B C) (syn_wf1 G A B)) (syn_wf1 (syn_ccom F G) A C) (syn_wa (syn_wfo F B C) (syn_wfo G A B)) (syn_wfo (syn_ccom F G) A C) p0000 p0001
  have p0003 :=
    @g_an4s (syn_wf1 F B C) (syn_wf1 G A B) (syn_wfo F B C) (syn_wfo G A B) (syn_wa (syn_wf1 (syn_ccom F G) A C) (syn_wfo (syn_ccom F G) A C)) p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F B C)))
  have p0005 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o G A B)))
  have p0006 :=
    @g_anbi12i (syn_wf1o F B C) (syn_wa (syn_wf1 F B C) (syn_wfo F B C)) (syn_wf1o G A B) (syn_wa (syn_wf1 G A B) (syn_wfo G A B)) p0004 p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o (syn_ccom F G) A C)))
  have p0008 :=
    @g_n_3imtr4i (syn_wa (syn_wa (syn_wf1 F B C) (syn_wfo F B C)) (syn_wa (syn_wf1 G A B) (syn_wfo G A B))) (syn_wa (syn_wf1 (syn_ccom F G) A C) (syn_wfo (syn_ccom F G) A C)) (syn_wa (syn_wf1o F B C) (syn_wf1o G A B)) (syn_wf1o (syn_ccom F G) A C) p0003 p0006 p0007
  exact p0008

noncomputable def g_f1ococnv2
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (.classEq (syn_ccom F (syn_ccnv F)) (syn_cres (syn_cid) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1ofun A B F
  have p0001 :=
    (by simpa [syn_wb, syn_wfun] using (Nominal.biimpRefl (syn_wfun F)))
  have p0002 :=
    @g_iss (syn_ccom F (syn_ccnv F))
  have p0003 :=
    @g_bitri (syn_wfun F) (syn_wss (syn_ccom F (syn_ccnv F)) (syn_cid)) (.classEq (syn_ccom F (syn_ccnv F)) (syn_cres (syn_cid) (syn_cdm (syn_ccom F (syn_ccnv F))))) p0001 p0002
  have p0004 :=
    @g_sylib (syn_wf1o F A B) (syn_wfun F) (.classEq (syn_ccom F (syn_ccnv F)) (syn_cres (syn_cid) (syn_cdm (syn_ccom F (syn_ccnv F))))) p0000 p0003
  have p0005 :=
    (by simpa [syn_cdm] using (Nominal.classEqRefl (syn_cdm F)))
  have p0006 :=
    @g_dmcoeq F (syn_ccnv F)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_dfrn4 F
  have p0009 :=
    @g_eqtr4i (syn_cdm (syn_ccom F (syn_ccnv F))) (syn_cdm (syn_ccnv F)) (syn_crn F) p0007 p0008
  have p0010 :=
    @g_f1ofo A B F
  have p0011 :=
    @g_forn A B F
  have p0012 :=
    @g_syl (syn_wf1o F A B) (syn_wfo F A B) (.classEq (syn_crn F) B) p0010 p0011
  have p0013 :=
    @g_syl5eq (syn_wf1o F A B) (syn_cdm (syn_ccom F (syn_ccnv F))) (syn_crn F) B p0009 p0012
  have p0014 :=
    @g_reseq2d (syn_wf1o F A B) (syn_cdm (syn_ccom F (syn_ccnv F))) B (syn_cid) p0013
  have p0015 :=
    @g_eqtrd (syn_wf1o F A B) (syn_ccom F (syn_ccnv F)) (syn_cres (syn_cid) (syn_cdm (syn_ccom F (syn_ccnv F)))) (syn_cres (syn_cid) B) p0004 p0014
  exact p0015

noncomputable def g_f1ococnv1
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (.classEq (syn_ccom (syn_ccnv F) F) (syn_cres (syn_cid) A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_cnvcnv F
  have p0001 :=
    @g_coeq2i (syn_ccnv (syn_ccnv F)) F (syn_ccnv F) p0000
  have p0002 :=
    @g_f1ocnv A B F
  have p0003 :=
    @g_f1ococnv2 B A (syn_ccnv F)
  have p0004 :=
    @g_syl (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A) (.classEq (syn_ccom (syn_ccnv F) (syn_ccnv (syn_ccnv F))) (syn_cres (syn_cid) A)) p0002 p0003
  have p0005 :=
    @g_syl5eqr (syn_wf1o F A B) (syn_ccom (syn_ccnv F) F) (syn_ccom (syn_ccnv F) (syn_ccnv (syn_ccnv F))) (syn_cres (syn_cid) A) p0001 p0004
  exact p0005

noncomputable def g_f1cnv
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1 F A B) (syn_wf1o (syn_ccnv F) (syn_crn F) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1f1orn A B F
  have p0001 :=
    @g_f1ocnv A (syn_crn F) F
  have p0002 :=
    @g_syl (syn_wf1 F A B) (syn_wf1o F A (syn_crn F)) (syn_wf1o (syn_ccnv F) (syn_crn F) A) p0000 p0001
  exact p0002

noncomputable def g_f10
    (A : Class) :
    Nominal.NPrf (syn_wf1 (syn_c0) (syn_c0) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_f0 A
  have p0001 :=
    @g_fun0
  have p0002 :=
    @g_cnv0
  have p0003 :=
    @g_funeqi (syn_ccnv (syn_c0)) (syn_c0) p0002
  have p0004 :=
    @g_mpbir (syn_wfun (syn_ccnv (syn_c0))) (syn_wfun (syn_c0)) p0001 p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 (syn_c0) (syn_c0) A)))
  have p0006 :=
    @g_mpbir2an (syn_wf1 (syn_c0) (syn_c0) A) (syn_wf (syn_c0) (syn_c0) A) (syn_wfun (syn_ccnv (syn_c0))) p0000 p0004 p0005
  exact p0006

noncomputable def g_f1o00
    (A : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wf1o F (syn_c0) A) (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_dff1o4 (syn_c0) A F
  have p0001 :=
    @g_fn0 F
  have p0002 :=
    @g_biimpi (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) p0001
  have p0003 :=
    @g_adantr (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) (syn_wfn (syn_ccnv F) A) p0002
  have p0004 :=
    @g_dm0
  have p0005 :=
    @g_cnveq F (syn_c0)
  have p0006 :=
    @g_cnv0
  have p0007 :=
    @g_syl6eq (.classEq F (syn_c0)) (syn_ccnv F) (syn_ccnv (syn_c0)) (syn_c0) p0005 p0006
  have p0008 :=
    @g_sylbi (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) (.classEq (syn_ccnv F) (syn_c0)) p0001 p0007
  have p0009 :=
    @g_fneq1d (syn_wfn F (syn_c0)) A (syn_ccnv F) (syn_c0) p0008
  have p0010 :=
    @g_biimpa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A) (syn_wfn (syn_c0) A) p0009
  have p0011 :=
    @g_fndm A (syn_c0)
  have p0012 :=
    @g_syl (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A)) (syn_wfn (syn_c0) A) (.classEq (syn_cdm (syn_c0)) A) p0010 p0011
  have p0013 :=
    @g_syl5reqr (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A)) (syn_c0) (syn_cdm (syn_c0)) A p0004 p0012
  have p0014 :=
    @g_jca (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A)) (.classEq F (syn_c0)) (.classEq A (syn_c0)) p0003 p0013
  have p0015 :=
    @g_biimpri (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) p0001
  have p0016 :=
    @g_adantr (.classEq F (syn_c0)) (syn_wfn F (syn_c0)) (.classEq A (syn_c0)) p0015
  have p0017 :=
    @g_eqid (syn_c0)
  have p0018 :=
    @g_fn0 (syn_c0)
  have p0019 :=
    @g_mpbir (syn_wfn (syn_c0) (syn_c0)) (.classEq (syn_c0) (syn_c0)) p0017 p0018
  have p0020 :=
    @g_fneq1d (.classEq F (syn_c0)) A (syn_ccnv F) (syn_c0) p0007
  have p0021 :=
    @g_fneq2 A (syn_c0) (syn_c0)
  have p0022 :=
    @g_sylan9bb (.classEq F (syn_c0)) (syn_wfn (syn_ccnv F) A) (syn_wfn (syn_c0) A) (.classEq A (syn_c0)) (syn_wfn (syn_c0) (syn_c0)) p0020 p0021
  have p0023 :=
    @g_mpbiri (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0))) (syn_wfn (syn_ccnv F) A) (syn_wfn (syn_c0) (syn_c0)) p0019 p0022
  have p0024 :=
    @g_jca (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0))) (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A) p0016 p0023
  have p0025 :=
    @g_impbii (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A)) (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0))) p0014 p0024
  have p0026 :=
    @g_bitri (syn_wf1o F (syn_c0) A) (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A)) (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0))) p0000 p0025
  exact p0026

noncomputable def g_f1o0
     :
    Nominal.NPrf (syn_wf1o (syn_c0) (syn_c0) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_f10 (syn_c0)
  have p0001 :=
    @g_fun0
  have p0002 :=
    @g_dm0
  have p0003 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_c0) (syn_c0))))
  have p0004 :=
    @g_mpbir2an (syn_wfn (syn_c0) (syn_c0)) (syn_wfun (syn_c0)) (.classEq (syn_cdm (syn_c0)) (syn_c0)) p0001 p0002 p0003
  have p0005 :=
    @g_rn0
  have p0006 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo (syn_c0) (syn_c0) (syn_c0))))
  have p0007 :=
    @g_mpbir2an (syn_wfo (syn_c0) (syn_c0) (syn_c0)) (syn_wfn (syn_c0) (syn_c0)) (.classEq (syn_crn (syn_c0)) (syn_c0)) p0004 p0005 p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o (syn_c0) (syn_c0) (syn_c0))))
  have p0009 :=
    @g_mpbir2an (syn_wf1o (syn_c0) (syn_c0) (syn_c0)) (syn_wf1 (syn_c0) (syn_c0) (syn_c0)) (syn_wfo (syn_c0) (syn_c0) (syn_c0)) p0000 p0007 p0008
  exact p0009

noncomputable def g_f1oi
    (A : Class) :
    Nominal.NPrf (syn_wf1o (syn_cres (syn_cid) A) A A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_fnresi A
  have p0001 :=
    @g_cnvresid A
  have p0002 :=
    @g_fneq1i A (syn_ccnv (syn_cres (syn_cid) A)) (syn_cres (syn_cid) A) p0001
  have p0003 :=
    @g_mpbir (syn_wfn (syn_ccnv (syn_cres (syn_cid) A)) A) (syn_wfn (syn_cres (syn_cid) A) A) p0000 p0002
  have p0004 :=
    @g_dff1o4 A A (syn_cres (syn_cid) A)
  have p0005 :=
    @g_mpbir2an (syn_wf1o (syn_cres (syn_cid) A) A A) (syn_wfn (syn_cres (syn_cid) A) A) (syn_wfn (syn_ccnv (syn_cres (syn_cid) A)) A) p0000 p0003 p0004
  exact p0005

noncomputable def g_f1ovi
     :
    Nominal.NPrf (syn_wf1o (syn_cid) (syn_cvv) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_funi
  have p0001 :=
    @g_dmi
  have p0002 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_cid) (syn_cvv))))
  have p0003 :=
    @g_mpbir2an (syn_wfn (syn_cid) (syn_cvv)) (syn_wfun (syn_cid)) (.classEq (syn_cdm (syn_cid)) (syn_cvv)) p0000 p0001 p0002
  have p0004 :=
    @g_cnvi
  have p0005 :=
    @g_fneq1i (syn_cvv) (syn_ccnv (syn_cid)) (syn_cid) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_ccnv (syn_cid)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0003 p0005
  have p0007 :=
    @g_dff1o4 (syn_cvv) (syn_cvv) (syn_cid)
  have p0008 :=
    @g_mpbir2an (syn_wf1o (syn_cid) (syn_cvv) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_ccnv (syn_cid)) (syn_cvv)) p0003 p0006 p0007
  exact p0008

noncomputable def g_f1osn
    (A : Class) (B : Class) (hyp_f1osn_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_f1osn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_fnsn A B hyp_f1osn_1 hyp_f1osn_2
  have p0001 :=
    @g_fnsn B A hyp_f1osn_2 hyp_f1osn_1
  have p0002 :=
    @g_cnvsn A B hyp_f1osn_1 hyp_f1osn_2
  have p0003 :=
    @g_fneq1i (syn_csn B) (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn (syn_cop B A)) p0002
  have p0004 :=
    @g_mpbir (syn_wfn (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn B)) (syn_wfn (syn_csn (syn_cop B A)) (syn_csn B)) p0001 p0003
  have p0005 :=
    @g_dff1o4 (syn_csn A) (syn_csn B) (syn_csn (syn_cop A B))
  have p0006 :=
    @g_mpbir2an (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) (syn_wfn (syn_csn (syn_cop A B)) (syn_csn A)) (syn_wfn (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn B)) p0000 p0004 p0005
  exact p0006

noncomputable def g_f1osng
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_V : a ∉ V.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_W : a ∉ W.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_V : b ∉ V.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_W : b ∉ W.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : a ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_sneq (.cv a) A
  have p0001 :=
    @g_f1oeq2 (syn_csn (.cv a)) (syn_csn A) (syn_csn (.cv b)) (syn_csn (syn_cop (.cv a) (.cv b)))
  have p0002 :=
    @g_syl (.classEq (.cv a) A) (.classEq (syn_csn (.cv a)) (syn_csn A)) (syn_wb (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn A) (syn_csn (.cv b)))) p0000 p0001
  have p0003 :=
    @g_opeq1 (.cv a) A (.cv b)
  have p0004 :=
    @g_sneq (syn_cop (.cv a) (.cv b)) (syn_cop A (.cv b))
  have p0005 :=
    @g_f1oeq1 (syn_csn A) (syn_csn (.cv b)) (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn (syn_cop A (.cv b)))
  have p0006 :=
    @g_n_3syl (.classEq (.cv a) A) (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop A (.cv b))) (.classEq (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn (syn_cop A (.cv b)))) (syn_wb (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn A) (syn_csn (.cv b))) (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b)))) p0003 p0004 p0005
  have p0007 :=
    @g_bitrd (.classEq (.cv a) A) (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn A) (syn_csn (.cv b))) (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b))) p0002 p0006
  have p0008 :=
    @g_sneq (.cv b) B
  have p0009 :=
    @g_f1oeq3 (syn_csn (.cv b)) (syn_csn B) (syn_csn A) (syn_csn (syn_cop A (.cv b)))
  have p0010 :=
    @g_syl (.classEq (.cv b) B) (.classEq (syn_csn (.cv b)) (syn_csn B)) (syn_wb (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b))) (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn B))) p0008 p0009
  have p0011 :=
    @g_opeq2 (.cv b) B A
  have p0012 :=
    @g_sneq (syn_cop A (.cv b)) (syn_cop A B)
  have p0013 :=
    @g_f1oeq1 (syn_csn A) (syn_csn B) (syn_csn (syn_cop A (.cv b))) (syn_csn (syn_cop A B))
  have p0014 :=
    @g_n_3syl (.classEq (.cv b) B) (.classEq (syn_cop A (.cv b)) (syn_cop A B)) (.classEq (syn_csn (syn_cop A (.cv b))) (syn_csn (syn_cop A B))) (syn_wb (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn B)) (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B))) p0011 p0012 p0013
  have p0015 :=
    @g_bitrd (.classEq (.cv b) B) (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b))) (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn B)) (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) p0010 p0014
  have p0016 :=
    @g_vex a
  have p0017 :=
    @g_vex b
  have p0018 :=
    @g_f1osn (.cv a) (.cv b) p0016 p0017
  have p0019 :=
    @g_vtocl2g (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b))) (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) a b A B V W dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0007 p0015 p0018
  exact p0019

noncomputable def g_fv2
    (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cfv F A) (syn_cuni (.cab x (.all y (syn_wb (syn_wbr A F (.cv y)) (.objEq y x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ F.fv
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_wbr A F (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_x_y, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv y A F dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_dfiota2 (syn_wbr A F (.cv y)) y x dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_eqtri (syn_cfv F A) (syn_cio y (syn_wbr A F (.cv y))) (syn_cuni (.cab x (.all y (syn_wb (syn_wbr A F (.cv y)) (.objEq y x))))) p0000 p0001
  exact p0002

noncomputable def g_fvprc
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (.neg (.classMem A (syn_cvv))) (.classEq (syn_cfv F A) (syn_c0))) := by
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
  have dv_cache_0002 : x ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_euex (syn_wbr A F (.cv x)) x
  have p0002 :=
    @g_brex A (.cv x) F
  have p0003 :=
    @g_simpld (syn_wbr A F (.cv x)) (.classMem A (syn_cvv)) (.classMem (.cv x) (syn_cvv)) p0002
  have p0004 :=
    @g_exlimiv (syn_wbr A F (.cv x)) (.classMem A (syn_cvv)) x dv_cache_0003 p0003
  have p0005 :=
    @g_syl (syn_weu x (syn_wbr A F (.cv x))) (syn_wex x (syn_wbr A F (.cv x))) (.classMem A (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_con3i (syn_weu x (syn_wbr A F (.cv x))) (.classMem A (syn_cvv)) p0005
  have p0007 :=
    @g_iotanul (syn_wbr A F (.cv x)) x
  have p0008 :=
    @g_syl (.neg (.classMem A (syn_cvv))) (.neg (syn_weu x (syn_wbr A F (.cv x)))) (.classEq (syn_cio x (syn_wbr A F (.cv x))) (syn_c0)) p0006 p0007
  have p0009 :=
    @g_syl5eq (.neg (.classMem A (syn_cvv))) (syn_cfv F A) (syn_cio x (syn_wbr A F (.cv x))) (syn_c0) p0000 p0008
  exact p0009

noncomputable def g_elfv
    (x : Var) (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cfv F B)) (syn_wex x (syn_wa (.classMem A (.cv x)) (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fv2 x y B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eleq2i (syn_cfv F B) (syn_cuni (.cab x (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x))))) A p0000
  have p0002 :=
    @g_eluniab (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x))) x A dv_cache_0006
  have p0003 :=
    @g_bitri (.classMem A (syn_cfv F B)) (.classMem A (syn_cuni (.cab x (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x)))))) (syn_wex x (syn_wa (.classMem A (.cv x)) (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x))))) p0001 p0002
  exact p0003

noncomputable def g_fveq1
    (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (.classEq (syn_cfv F A) (syn_cfv G A))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq F G)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_breq A (.cv x) F G
  have p0001 :=
    @g_iotabidv (.classEq F G) (syn_wbr A F (.cv x)) (syn_wbr A G (.cv x)) x dv_cache_0001 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F dv_cache_0002 dv_cache_0003
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A G dv_cache_0002 dv_cache_0004
  have p0004 :=
    @g_n_3eqtr4g (.classEq F G) (syn_cio x (syn_wbr A F (.cv x))) (syn_cio x (syn_wbr A G (.cv x))) (syn_cfv F A) (syn_cfv G A) p0001 p0002 p0003
  exact p0004

noncomputable def g_fveq2
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cfv F A) (syn_cfv F B))) := by
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
  have dv_cache_0001 : x ∉ ((Wff.classEq A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_breq1 A B (.cv x) F
  have p0001 :=
    @g_iotabidv (.classEq A B) (syn_wbr A F (.cv x)) (syn_wbr B F (.cv x)) x dv_cache_0001 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F dv_cache_0002 dv_cache_0003
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x B F dv_cache_0004 dv_cache_0003
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cio x (syn_wbr A F (.cv x))) (syn_cio x (syn_wbr B F (.cv x))) (syn_cfv F A) (syn_cfv F B) p0001 p0002 p0003
  exact p0004

noncomputable def g_fveq1i
    (A : Class) (F : Class) (G : Class) (hyp_fveq1i_1 : Nominal.NPrf (.classEq F G)) :
    Nominal.NPrf (.classEq (syn_cfv F A) (syn_cfv G A)) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fveq1 A F G
  have p0001 :=
    Nominal.mp hyp_fveq1i_1 p0000
  exact p0001

noncomputable def g_fveq1d
    (ph : Wff) (A : Class) (F : Class) (G : Class) (hyp_fveq1d_1 : Nominal.NPrf (.imp ph (.classEq F G))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cfv F A) (syn_cfv G A))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fveq1 A F G
  have p0001 :=
    @g_syl ph (.classEq F G) (.classEq (syn_cfv F A) (syn_cfv G A)) hyp_fveq1d_1 p0000
  exact p0001

noncomputable def g_fveq2i
    (A : Class) (B : Class) (F : Class) (hyp_fveq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cfv F A) (syn_cfv F B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fveq2 A B F
  have p0001 :=
    Nominal.mp hyp_fveq2i_1 p0000
  exact p0001

noncomputable def g_fveq2d
    (ph : Wff) (A : Class) (B : Class) (F : Class) (hyp_fveq2d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cfv F A) (syn_cfv F B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fveq2 A B F
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cfv F A) (syn_cfv F B)) hyp_fveq2d_1 p0000
  exact p0001

noncomputable def g_fvex
    (A : Class) (F : Class) :
    Nominal.NPrf (.classMem (syn_cfv F A) (syn_cvv)) := by
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
  have dv_cache_0002 : x ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_iotaex (syn_wbr A F (.cv x)) x
  have p0002 :=
    @g_eqeltri (syn_cfv F A) (syn_cio x (syn_wbr A F (.cv x))) (syn_cvv) p0000 p0001
  exact p0002

#print axioms g_fvex

end NFChoice.DirectNominalPrf.WPPReplay
