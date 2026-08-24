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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk011Compact001Part015

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

noncomputable def g_feq2
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf F A C) (syn_wf F B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_fneq2 A B F
  have p0001 :=
    @g_anbi1d (.classEq A B) (syn_wfn F A) (syn_wfn F B) (syn_wss (syn_crn F) C) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A C)))
  have p0003 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F B C)))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) C)) (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C)) (syn_wf F A C) (syn_wf F B C) p0001 p0002 p0003
  exact p0004

noncomputable def g_feq3
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf F C A) (syn_wf F C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_sseq2 A B (syn_crn F)
  have p0001 :=
    @g_anbi2d (.classEq A B) (syn_wss (syn_crn F) A) (syn_wss (syn_crn F) B) (syn_wfn F C) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F C A)))
  have p0003 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F C B)))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfn F C) (syn_wss (syn_crn F) A)) (syn_wa (syn_wfn F C) (syn_wss (syn_crn F) B)) (syn_wf F C A) (syn_wf F C B) p0001 p0002 p0003
  exact p0004

noncomputable def g_feq1i
    (A : Class) (B : Class) (F : Class) (G : Class) (hyp_feq1i_1 : Nominal.NPrf (.classEq F G)) :
    Nominal.NPrf (syn_wb (syn_wf F A B) (syn_wf G A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_feq1 A B F G
  have p0001 :=
    Nominal.mp hyp_feq1i_1 p0000
  exact p0001

noncomputable def g_feq2i
    (A : Class) (B : Class) (C : Class) (F : Class) (hyp_feq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wf F A C) (syn_wf F B C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_feq2 A B C F
  have p0001 :=
    Nominal.mp hyp_feq2i_1 p0000
  exact p0001

noncomputable def g_ffn
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wfn F A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0001 :=
    @g_simplbi (syn_wf F A B) (syn_wfn F A) (syn_wss (syn_crn F) B) p0000
  exact p0001

noncomputable def g_dffn2
    (A : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wf F A (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_ssv (syn_crn F)
  have p0001 :=
    @g_biantru (syn_wss (syn_crn F) (syn_cvv)) (syn_wfn F A) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A (syn_cvv))))
  have p0003 :=
    @g_bitr4i (syn_wfn F A) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) (syn_cvv))) (syn_wf F A (syn_cvv)) p0001 p0002
  exact p0003

noncomputable def g_ffun
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wfun F)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_ffn A B F
  have p0001 :=
    @g_fnfun A F
  have p0002 :=
    @g_syl (syn_wf F A B) (syn_wfn F A) (syn_wfun F) p0000 p0001
  exact p0002

noncomputable def g_fdm
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (.classEq (syn_cdm F) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_ffn A B F
  have p0001 :=
    @g_fndm A F
  have p0002 :=
    @g_syl (syn_wf F A B) (syn_wfn F A) (.classEq (syn_cdm F) A) p0000 p0001
  exact p0002

noncomputable def g_frn
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wss (syn_crn F) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0001 :=
    @g_simprbi (syn_wf F A B) (syn_wfn F A) (syn_wss (syn_crn F) B) p0000
  exact p0001

noncomputable def g_dffn3
    (A : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wf F A (syn_crn F))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_ssid (syn_crn F)
  have p0001 :=
    @g_biantru (syn_wss (syn_crn F) (syn_crn F)) (syn_wfn F A) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A (syn_crn F))))
  have p0003 :=
    @g_bitr4i (syn_wfn F A) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) (syn_crn F))) (syn_wf F A (syn_crn F)) p0001 p0002
  exact p0003

noncomputable def g_fss
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf F A B) (syn_wss B C)) (syn_wf F A C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_sstr2 (syn_crn F) B C
  have p0001 :=
    @g_com12 (syn_wss (syn_crn F) B) (syn_wss B C) (syn_wss (syn_crn F) C) p0000
  have p0002 :=
    @g_anim2d (syn_wss B C) (syn_wss (syn_crn F) B) (syn_wss (syn_crn F) C) (syn_wfn F A) p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0004 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A C)))
  have p0005 :=
    @g_n_3imtr4g (syn_wss B C) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) C)) (syn_wf F A B) (syn_wf F A C) p0002 p0003 p0004
  have p0006 :=
    @g_impcom (syn_wss B C) (syn_wf F A B) (syn_wf F A C) p0005
  exact p0006

noncomputable def g_fco
    (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf F B C) (syn_wf G A B)) (syn_wf (syn_ccom F G) A C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fnco B A F G
  have p0001 :=
    @g_n_3expib (syn_wfn F B) (syn_wfn G A) (syn_wss (syn_crn G) B) (syn_wfn (syn_ccom F G) A) p0000
  have p0002 :=
    @g_adantr (syn_wfn F B) (.imp (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)) (syn_wfn (syn_ccom F G) A)) (syn_wss (syn_crn F) C) p0001
  have p0003 :=
    @g_rncoss F G
  have p0004 :=
    @g_sstr (syn_crn (syn_ccom F G)) (syn_crn F) C
  have p0005 :=
    @g_mpan (syn_wss (syn_crn (syn_ccom F G)) (syn_crn F)) (syn_wss (syn_crn F) C) (syn_wss (syn_crn (syn_ccom F G)) C) p0003 p0004
  have p0006 :=
    @g_adantl (syn_wss (syn_crn F) C) (syn_wss (syn_crn (syn_ccom F G)) C) (syn_wfn F B) p0005
  have p0007 :=
    @g_jctird (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C)) (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)) (syn_wfn (syn_ccom F G) A) (syn_wss (syn_crn (syn_ccom F G)) C) p0002 p0006
  have p0008 :=
    @g_imp (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C)) (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)) (syn_wa (syn_wfn (syn_ccom F G) A) (syn_wss (syn_crn (syn_ccom F G)) C)) p0007
  have p0009 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F B C)))
  have p0010 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf G A B)))
  have p0011 :=
    @g_anbi12i (syn_wf F B C) (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C)) (syn_wf G A B) (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)) p0009 p0010
  have p0012 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_ccom F G) A C)))
  have p0013 :=
    @g_n_3imtr4i (syn_wa (syn_wa (syn_wfn F B) (syn_wss (syn_crn F) C)) (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B))) (syn_wa (syn_wfn (syn_ccom F G) A) (syn_wss (syn_crn (syn_ccom F G)) C)) (syn_wa (syn_wf F B C) (syn_wf G A B)) (syn_wf (syn_ccom F G) A C) p0008 p0011 p0012
  exact p0013

noncomputable def g_fssxp
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (syn_wss F (syn_cxp A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_ssdmrn F
  have p0001 :=
    @g_fdm A B F
  have p0002 :=
    @g_eqimss (syn_cdm F) A
  have p0003 :=
    @g_syl (syn_wf F A B) (.classEq (syn_cdm F) A) (syn_wss (syn_cdm F) A) p0001 p0002
  have p0004 :=
    @g_frn A B F
  have p0005 :=
    @g_xpss12 (syn_cdm F) A (syn_crn F) B
  have p0006 :=
    @g_syl2anc (syn_wf F A B) (syn_wss (syn_cdm F) A) (syn_wss (syn_crn F) B) (syn_wss (syn_cxp (syn_cdm F) (syn_crn F)) (syn_cxp A B)) p0003 p0004 p0005
  have p0007 :=
    @g_syl5ss (syn_wf F A B) F (syn_cxp (syn_cdm F) (syn_crn F)) (syn_cxp A B) p0000 p0006
  exact p0007

noncomputable def g_opelf
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf F A B) (.classMem (syn_cop C D) F)) (syn_wa (.classMem C A) (.classMem D B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  have p0000 :=
    @g_fssxp A B F
  have p0001 :=
    @g_sseld (syn_wf F A B) F (syn_cxp A B) (syn_cop C D) p0000
  have p0002 :=
    @g_opelxp C D A B
  have p0003 :=
    @g_syl6ib (syn_wf F A B) (.classMem (syn_cop C D) F) (.classMem (syn_cop C D) (syn_cxp A B)) (syn_wa (.classMem C A) (.classMem D B)) p0001 p0002
  have p0004 :=
    @g_imp (syn_wf F A B) (.classMem (syn_cop C D) F) (syn_wa (.classMem C A) (.classMem D B)) p0003
  exact p0004

noncomputable def g_fun
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wf F A C) (syn_wf G B D)) (.classEq (syn_cin A B) (syn_c0))) (syn_wf (syn_cun F G) (syn_cun A B) (syn_cun C D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fnun A B F G
  have p0001 :=
    @g_expcom (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A B)) p0000
  have p0002 :=
    @g_rnun F G
  have p0003 :=
    @g_unss12 (syn_crn F) C (syn_crn G) D
  have p0004 :=
    @g_syl5eqss (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D)) (syn_crn (syn_cun F G)) (syn_cun (syn_crn F) (syn_crn G)) (syn_cun C D) p0002 p0003
  have p0005 :=
    @g_a1i (.imp (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D)) (syn_wss (syn_crn (syn_cun F G)) (syn_cun C D))) (.classEq (syn_cin A B) (syn_c0)) p0004
  have p0006 :=
    @g_anim12d (.classEq (syn_cin A B) (syn_c0)) (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_wfn (syn_cun F G) (syn_cun A B)) (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D)) (syn_wss (syn_crn (syn_cun F G)) (syn_cun C D)) p0001 p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A C)))
  have p0008 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf G B D)))
  have p0009 :=
    @g_anbi12i (syn_wf F A C) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) C)) (syn_wf G B D) (syn_wa (syn_wfn G B) (syn_wss (syn_crn G) D)) p0007 p0008
  have p0010 :=
    @g_an4 (syn_wfn F A) (syn_wss (syn_crn F) C) (syn_wfn G B) (syn_wss (syn_crn G) D)
  have p0011 :=
    @g_bitri (syn_wa (syn_wf F A C) (syn_wf G B D)) (syn_wa (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) C)) (syn_wa (syn_wfn G B) (syn_wss (syn_crn G) D))) (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D))) p0009 p0010
  have p0012 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cun F G) (syn_cun A B) (syn_cun C D))))
  have p0013 :=
    @g_n_3imtr4g (.classEq (syn_cin A B) (syn_c0)) (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_wa (syn_wss (syn_crn F) C) (syn_wss (syn_crn G) D))) (syn_wa (syn_wfn (syn_cun F G) (syn_cun A B)) (syn_wss (syn_crn (syn_cun F G)) (syn_cun C D))) (syn_wa (syn_wf F A C) (syn_wf G B D)) (syn_wf (syn_cun F G) (syn_cun A B) (syn_cun C D)) p0006 p0011 p0012
  have p0014 :=
    @g_impcom (.classEq (syn_cin A B) (syn_c0)) (syn_wa (syn_wf F A C) (syn_wf G B D)) (syn_wf (syn_cun F G) (syn_cun A B) (syn_cun C D)) p0013
  exact p0014

noncomputable def g_fnfco
    (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (syn_wf G B A)) (syn_wfn (syn_ccom F G) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf G B A)))
  have p0001 :=
    @g_fnco A B F G
  have p0002 :=
    @g_n_3expb (syn_wfn F A) (syn_wfn G B) (syn_wss (syn_crn G) A) (syn_wfn (syn_ccom F G) B) p0001
  have p0003 :=
    @g_sylan2b (syn_wf G B A) (syn_wfn F A) (syn_wa (syn_wfn G B) (syn_wss (syn_crn G) A)) (syn_wfn (syn_ccom F G) B) p0000 p0002
  exact p0003

noncomputable def g_fssres
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf F A B) (syn_wss C A)) (syn_wf (syn_cres F C) C B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0001 :=
    @g_fnssres A C F
  have p0002 :=
    @g_resss F C
  have p0003 :=
    @g_rnss (syn_cres F C) F
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_sstr (syn_crn (syn_cres F C)) (syn_crn F) B
  have p0006 :=
    @g_mpan (syn_wss (syn_crn (syn_cres F C)) (syn_crn F)) (syn_wss (syn_crn F) B) (syn_wss (syn_crn (syn_cres F C)) B) p0004 p0005
  have p0007 :=
    @g_anim12i (syn_wa (syn_wfn F A) (syn_wss C A)) (syn_wfn (syn_cres F C) C) (syn_wss (syn_crn F) B) (syn_wss (syn_crn (syn_cres F C)) B) p0001 p0006
  have p0008 :=
    @g_an32s (syn_wfn F A) (syn_wss C A) (syn_wss (syn_crn F) B) (syn_wa (syn_wfn (syn_cres F C) C) (syn_wss (syn_crn (syn_cres F C)) B)) p0007
  have p0009 :=
    @g_sylanb (syn_wf F A B) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) (syn_wss C A) (syn_wa (syn_wfn (syn_cres F C) C) (syn_wss (syn_crn (syn_cres F C)) B)) p0000 p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cres F C) C B)))
  have p0011 :=
    @g_sylibr (syn_wa (syn_wf F A B) (syn_wss C A)) (syn_wa (syn_wfn (syn_cres F C) C) (syn_wss (syn_crn (syn_cres F C)) B)) (syn_wf (syn_cres F C) C B) p0009 p0010
  exact p0011

noncomputable def g_fcoi1
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf F A B) (.classEq (syn_ccom F (syn_cres (syn_cid) A)) F)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_coi1 F
  have p0001 :=
    @g_reseq1i (syn_ccom F (syn_cid)) F A p0000
  have p0002 :=
    @g_resco F (syn_cid) A
  have p0003 :=
    @g_eqtr3i (syn_cres (syn_ccom F (syn_cid)) A) (syn_cres F A) (syn_ccom F (syn_cres (syn_cid) A)) p0001 p0002
  have p0004 :=
    @g_ffn A B F
  have p0005 :=
    @g_fnresdm A F
  have p0006 :=
    @g_syl (syn_wf F A B) (syn_wfn F A) (.classEq (syn_cres F A) F) p0004 p0005
  have p0007 :=
    @g_syl5eqr (syn_wf F A B) (syn_ccom F (syn_cres (syn_cid) A)) (syn_cres F A) F p0003 p0006
  exact p0007

noncomputable def g_feu
    (y : Var) (A : Class) (B : Class) (C : Class) (F : Class) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wf F A B) (.classMem C A)) (syn_wreu y B (.classMem (syn_cop C (.cv y)) F))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have dv_cache_0001 : y ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_wf F A B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ffn A B F
  have p0001 :=
    @g_fneu2 y A C F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_sylan (syn_wf F A B) (syn_wfn F A) (.classMem C A) (syn_weu y (.classMem (syn_cop C (.cv y)) F)) p0000 p0001
  have p0003 :=
    @g_opelf A B C (.cv y) F
  have p0004 :=
    @g_simprd (syn_wa (syn_wf F A B) (.classMem (syn_cop C (.cv y)) F)) (.classMem C A) (.classMem (.cv y) B) p0003
  have p0005 :=
    @g_ex (syn_wf F A B) (.classMem (syn_cop C (.cv y)) F) (.classMem (.cv y) B) p0004
  have p0006 :=
    @g_pm4_71rd (syn_wf F A B) (.classMem (syn_cop C (.cv y)) F) (.classMem (.cv y) B) p0005
  have p0007 :=
    @g_eubidv (syn_wf F A B) (.classMem (syn_cop C (.cv y)) F) (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop C (.cv y)) F)) y dv_cache_0003 p0006
  have p0008 :=
    @g_adantr (syn_wf F A B) (syn_wb (syn_weu y (.classMem (syn_cop C (.cv y)) F)) (syn_weu y (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop C (.cv y)) F)))) (.classMem C A) p0007
  have p0009 :=
    @g_mpbid (syn_wa (syn_wf F A B) (.classMem C A)) (syn_weu y (.classMem (syn_cop C (.cv y)) F)) (syn_weu y (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop C (.cv y)) F))) p0002 p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wreu] using (Nominal.biimpRefl (syn_wreu y B (.classMem (syn_cop C (.cv y)) F))))
  have p0011 :=
    @g_sylibr (syn_wa (syn_wf F A B) (.classMem C A)) (syn_weu y (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop C (.cv y)) F))) (syn_wreu y B (.classMem (syn_cop C (.cv y)) F)) p0009 p0010
  exact p0011

noncomputable def g_f0
    (A : Class) :
    Nominal.NPrf (syn_wf (syn_c0) (syn_c0) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_fun0
  have p0001 :=
    @g_dm0
  have p0002 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_c0) (syn_c0))))
  have p0003 :=
    @g_mpbir2an (syn_wfn (syn_c0) (syn_c0)) (syn_wfun (syn_c0)) (.classEq (syn_cdm (syn_c0)) (syn_c0)) p0000 p0001 p0002
  have p0004 :=
    @g_rn0
  have p0005 :=
    @g_n_0ss A
  have p0006 :=
    @g_eqsstri (syn_crn (syn_c0)) (syn_c0) A p0004 p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_c0) (syn_c0) A)))
  have p0008 :=
    @g_mpbir2an (syn_wf (syn_c0) (syn_c0) A) (syn_wfn (syn_c0) (syn_c0)) (syn_wss (syn_crn (syn_c0)) A) p0003 p0006 p0007
  exact p0008

noncomputable def g_fconst
    (A : Class) (B : Class) (hyp_fconst_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_fconstopab x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_fnopab2 x y A B (syn_cxp A (syn_csn B)) dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0005 hyp_fconst_1 p0000
  have p0002 :=
    @g_rnxpss A (syn_csn B)
  have p0003 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))))
  have p0004 :=
    @g_mpbir2an (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) (syn_wfn (syn_cxp A (syn_csn B)) A) (syn_wss (syn_crn (syn_cxp A (syn_csn B))) (syn_csn B)) p0001 p0002 p0003
  exact p0004

noncomputable def g_fconstg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
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
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_sneq (.cv x) B
  have p0001 :=
    @g_xpeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) A p0000
  have p0002 :=
    @g_feq1 A (syn_csn (.cv x)) (syn_cxp A (syn_csn (.cv x))) (syn_cxp A (syn_csn B))
  have p0003 :=
    @g_feq3 (syn_csn (.cv x)) (syn_csn B) A (syn_cxp A (syn_csn B))
  have p0004 :=
    @g_sylan9bb (.classEq (syn_cxp A (syn_csn (.cv x))) (syn_cxp A (syn_csn B))) (syn_wf (syn_cxp A (syn_csn (.cv x))) A (syn_csn (.cv x))) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn (.cv x))) (.classEq (syn_csn (.cv x)) (syn_csn B)) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) p0002 p0003
  have p0005 :=
    @g_syl2anc (.classEq (.cv x) B) (.classEq (syn_cxp A (syn_csn (.cv x))) (syn_cxp A (syn_csn B))) (.classEq (syn_csn (.cv x)) (syn_csn B)) (syn_wb (syn_wf (syn_cxp A (syn_csn (.cv x))) A (syn_csn (.cv x))) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))) p0001 p0000 p0004
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_fconst A (.cv x) p0006
  have p0008 :=
    @g_vtoclg (syn_wf (syn_cxp A (syn_csn (.cv x))) A (syn_csn (.cv x))) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) x B V dv_cache_0001 dv_cache_0002 p0005 p0007
  exact p0008

noncomputable def g_fnconstg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (syn_wfn (syn_cxp A (syn_csn B)) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  have p0000 :=
    @g_fconstg A B V
  have p0001 :=
    @g_ffn A (syn_csn B) (syn_cxp A (syn_csn B))
  have p0002 :=
    @g_syl (.classMem B V) (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) (syn_wfn (syn_cxp A (syn_csn B)) A) p0000 p0001
  exact p0002

noncomputable def g_f1eq1
    (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wf1 F A B) (syn_wf1 G A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_feq1 A B F G
  have p0001 :=
    @g_cnveq F G
  have p0002 :=
    @g_funeqd (.classEq F G) (syn_ccnv F) (syn_ccnv G) p0001
  have p0003 :=
    @g_anbi12d (.classEq F G) (syn_wf F A B) (syn_wf G A B) (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv G)) p0000 p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A B)))
  have p0005 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 G A B)))
  have p0006 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))) (syn_wa (syn_wf G A B) (syn_wfun (syn_ccnv G))) (syn_wf1 F A B) (syn_wf1 G A B) p0003 p0004 p0005
  exact p0006

noncomputable def g_f1eq2
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf1 F A C) (syn_wf1 F B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_feq2 A B C F
  have p0001 :=
    @g_anbi1d (.classEq A B) (syn_wf F A C) (syn_wf F B C) (syn_wfun (syn_ccnv F)) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A C)))
  have p0003 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F B C)))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wf F A C) (syn_wfun (syn_ccnv F))) (syn_wa (syn_wf F B C) (syn_wfun (syn_ccnv F))) (syn_wf1 F A C) (syn_wf1 F B C) p0001 p0002 p0003
  exact p0004

noncomputable def g_f1eq3
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf1 F C A) (syn_wf1 F C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_feq3 A B C F
  have p0001 :=
    @g_anbi1d (.classEq A B) (syn_wf F C A) (syn_wf F C B) (syn_wfun (syn_ccnv F)) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F C A)))
  have p0003 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F C B)))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wf F C A) (syn_wfun (syn_ccnv F))) (syn_wa (syn_wf F C B) (syn_wfun (syn_ccnv F))) (syn_wf1 F C A) (syn_wf1 F C B) p0001 p0002 p0003
  exact p0004

noncomputable def g_dff12
    (x : Var) (y : Var) (A : Class) (B : Class) (F : Class) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wf1 F A B) (syn_wa (syn_wf F A B) (.all y (syn_wmo x (syn_wbr (.cv x) F (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : x ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A B)))
  have p0001 :=
    @g_funcnv2 x y F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_anbi2i (syn_wfun (syn_ccnv F)) (.all y (syn_wmo x (syn_wbr (.cv x) F (.cv y)))) (syn_wf F A B) p0001
  have p0003 :=
    @g_bitri (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))) (syn_wa (syn_wf F A B) (.all y (syn_wmo x (syn_wbr (.cv x) F (.cv y))))) p0000 p0002
  exact p0003

noncomputable def g_f1f
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1 F A B) (syn_wf F A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A B)))
  have p0001 :=
    @g_simplbi (syn_wf1 F A B) (syn_wf F A B) (syn_wfun (syn_ccnv F)) p0000
  exact p0001

noncomputable def g_f1fn
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1 F A B) (syn_wfn F A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1f A B F
  have p0001 :=
    @g_ffn A B F
  have p0002 :=
    @g_syl (syn_wf1 F A B) (syn_wf F A B) (syn_wfn F A) p0000 p0001
  exact p0002

noncomputable def g_f1ss
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1 F A B) (syn_wss B C)) (syn_wf1 F A C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_f1f A B F
  have p0001 :=
    @g_fss A B C F
  have p0002 :=
    @g_sylan (syn_wf1 F A B) (syn_wf F A B) (syn_wss B C) (syn_wf F A C) p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A B)))
  have p0004 :=
    @g_simprbi (syn_wf1 F A B) (syn_wf F A B) (syn_wfun (syn_ccnv F)) p0003
  have p0005 :=
    @g_adantr (syn_wf1 F A B) (syn_wfun (syn_ccnv F)) (syn_wss B C) p0004
  have p0006 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F A C)))
  have p0007 :=
    @g_sylanbrc (syn_wa (syn_wf1 F A B) (syn_wss B C)) (syn_wf F A C) (syn_wfun (syn_ccnv F)) (syn_wf1 F A C) p0002 p0005 p0006
  exact p0007

noncomputable def g_f1co
    (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1 F B C) (syn_wf1 G A B)) (syn_wf1 (syn_ccom F G) A C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fco A B C F G
  have p0001 :=
    @g_funco (syn_ccnv G) (syn_ccnv F)
  have p0002 :=
    @g_cnvco F G
  have p0003 :=
    @g_funeqi (syn_ccnv (syn_ccom F G)) (syn_ccom (syn_ccnv G) (syn_ccnv F)) p0002
  have p0004 :=
    @g_sylibr (syn_wa (syn_wfun (syn_ccnv G)) (syn_wfun (syn_ccnv F))) (syn_wfun (syn_ccom (syn_ccnv G) (syn_ccnv F))) (syn_wfun (syn_ccnv (syn_ccom F G))) p0001 p0003
  have p0005 :=
    @g_ancoms (syn_wfun (syn_ccnv G)) (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv (syn_ccom F G))) p0004
  have p0006 :=
    @g_anim12i (syn_wa (syn_wf F B C) (syn_wf G A B)) (syn_wf (syn_ccom F G) A C) (syn_wa (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv G))) (syn_wfun (syn_ccnv (syn_ccom F G))) p0000 p0005
  have p0007 :=
    @g_an4s (syn_wf F B C) (syn_wf G A B) (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv G)) (syn_wa (syn_wf (syn_ccom F G) A C) (syn_wfun (syn_ccnv (syn_ccom F G)))) p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 F B C)))
  have p0009 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 G A B)))
  have p0010 :=
    @g_anbi12i (syn_wf1 F B C) (syn_wa (syn_wf F B C) (syn_wfun (syn_ccnv F))) (syn_wf1 G A B) (syn_wa (syn_wf G A B) (syn_wfun (syn_ccnv G))) p0008 p0009
  have p0011 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 (syn_ccom F G) A C)))
  have p0012 :=
    @g_n_3imtr4i (syn_wa (syn_wa (syn_wf F B C) (syn_wfun (syn_ccnv F))) (syn_wa (syn_wf G A B) (syn_wfun (syn_ccnv G)))) (syn_wa (syn_wf (syn_ccom F G) A C) (syn_wfun (syn_ccnv (syn_ccom F G)))) (syn_wa (syn_wf1 F B C) (syn_wf1 G A B)) (syn_wf1 (syn_ccom F G) A C) p0007 p0010 p0011
  exact p0012

noncomputable def g_foeq1
    (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wfo F A B) (syn_wfo G A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fneq1 A F G
  have p0001 :=
    @g_rneq F G
  have p0002 :=
    @g_eqeq1d (.classEq F G) (syn_crn F) (syn_crn G) B p0001
  have p0003 :=
    @g_anbi12d (.classEq F G) (syn_wfn F A) (syn_wfn G A) (.classEq (syn_crn F) B) (.classEq (syn_crn G) B) p0000 p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F A B)))
  have p0005 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo G A B)))
  have p0006 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wa (syn_wfn G A) (.classEq (syn_crn G) B)) (syn_wfo F A B) (syn_wfo G A B) p0003 p0004 p0005
  exact p0006

noncomputable def g_foeq2
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wfo F A C) (syn_wfo F B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_fneq2 A B F
  have p0001 :=
    @g_anbi1d (.classEq A B) (syn_wfn F A) (syn_wfn F B) (.classEq (syn_crn F) C) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F A C)))
  have p0003 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F B C)))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) C)) (syn_wa (syn_wfn F B) (.classEq (syn_crn F) C)) (syn_wfo F A C) (syn_wfo F B C) p0001 p0002 p0003
  exact p0004

noncomputable def g_foeq3
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wfo F C A) (syn_wfo F C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_eqeq2 A B (syn_crn F)
  have p0001 :=
    @g_anbi2d (.classEq A B) (.classEq (syn_crn F) A) (.classEq (syn_crn F) B) (syn_wfn F C) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F C A)))
  have p0003 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F C B)))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfn F C) (.classEq (syn_crn F) A)) (syn_wa (syn_wfn F C) (.classEq (syn_crn F) B)) (syn_wfo F C A) (syn_wfo F C B) p0001 p0002 p0003
  exact p0004

noncomputable def g_fof
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (syn_wf F A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_eqimss (syn_crn F) B
  have p0001 :=
    @g_anim2i (.classEq (syn_crn F) B) (syn_wss (syn_crn F) B) (syn_wfn F A) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F A B)))
  have p0003 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0004 :=
    @g_n_3imtr4i (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) (syn_wfo F A B) (syn_wf F A B) p0001 p0002 p0003
  exact p0004

noncomputable def g_fofun
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (syn_wfun F)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fof A B F
  have p0001 :=
    @g_ffun A B F
  have p0002 :=
    @g_syl (syn_wfo F A B) (syn_wf F A B) (syn_wfun F) p0000 p0001
  exact p0002

noncomputable def g_fofn
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (syn_wfn F A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fof A B F
  have p0001 :=
    @g_ffn A B F
  have p0002 :=
    @g_syl (syn_wfo F A B) (syn_wf F A B) (syn_wfn F A) p0000 p0001
  exact p0002

noncomputable def g_forn
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (.classEq (syn_crn F) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F A B)))
  have p0001 :=
    @g_simprbi (syn_wfo F A B) (syn_wfn F A) (.classEq (syn_crn F) B) p0000
  exact p0001

noncomputable def g_dffo2
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wfo F A B) (syn_wa (syn_wf F A B) (.classEq (syn_crn F) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fof A B F
  have p0001 :=
    @g_forn A B F
  have p0002 :=
    @g_jca (syn_wfo F A B) (syn_wf F A B) (.classEq (syn_crn F) B) p0000 p0001
  have p0003 :=
    @g_ffn A B F
  have p0004 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F A B)))
  have p0005 :=
    @g_biimpri (syn_wfo F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) p0004
  have p0006 :=
    @g_sylan (syn_wf F A B) (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wfo F A B) p0003 p0005
  have p0007 :=
    @g_impbii (syn_wfo F A B) (syn_wa (syn_wf F A B) (.classEq (syn_crn F) B)) p0002 p0006
  exact p0007

noncomputable def g_foima
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfo F A B) (.classEq (syn_cima F A) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_imadmrn F
  have p0001 :=
    @g_fof A B F
  have p0002 :=
    @g_fdm A B F
  have p0003 :=
    @g_imaeq2 (syn_cdm F) A F
  have p0004 :=
    @g_n_3syl (syn_wfo F A B) (syn_wf F A B) (.classEq (syn_cdm F) A) (.classEq (syn_cima F (syn_cdm F)) (syn_cima F A)) p0001 p0002 p0003
  have p0005 :=
    @g_syl5reqr (syn_wfo F A B) (syn_crn F) (syn_cima F (syn_cdm F)) (syn_cima F A) p0000 p0004
  have p0006 :=
    @g_forn A B F
  have p0007 :=
    @g_eqtrd (syn_wfo F A B) (syn_cima F A) (syn_crn F) B p0005 p0006
  exact p0007

noncomputable def g_dffn4
    (A : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wfo F A (syn_crn F))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_eqid (syn_crn F)
  have p0001 :=
    @g_biantru (.classEq (syn_crn F) (syn_crn F)) (syn_wfn F A) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F A (syn_crn F))))
  have p0003 :=
    @g_bitr4i (syn_wfn F A) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) (syn_crn F))) (syn_wfo F A (syn_crn F)) p0001 p0002
  exact p0003

noncomputable def g_fores
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wfo (syn_cres F A) A (syn_cima F A))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_funres A F
  have p0001 :=
    @g_anim1i (syn_wfun F) (syn_wfun (syn_cres F A)) (syn_wss A (syn_cdm F)) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_cres F A) A)))
  have p0003 :=
    @g_dfima3 F A
  have p0004 :=
    @g_eqcomi (syn_cima F A) (syn_crn (syn_cres F A)) p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo (syn_cres F A) A (syn_cima F A))))
  have p0006 :=
    @g_mpbiran2 (syn_wfo (syn_cres F A) A (syn_cima F A)) (syn_wfn (syn_cres F A) A) (.classEq (syn_crn (syn_cres F A)) (syn_cima F A)) p0004 p0005
  have p0007 :=
    @g_ssdmres A F
  have p0008 :=
    @g_anbi2i (syn_wss A (syn_cdm F)) (.classEq (syn_cdm (syn_cres F A)) A) (syn_wfun (syn_cres F A)) p0007
  have p0009 :=
    @g_n_3bitr4i (syn_wfn (syn_cres F A) A) (syn_wa (syn_wfun (syn_cres F A)) (.classEq (syn_cdm (syn_cres F A)) A)) (syn_wfo (syn_cres F A) A (syn_cima F A)) (syn_wa (syn_wfun (syn_cres F A)) (syn_wss A (syn_cdm F))) p0002 p0006 p0008
  have p0010 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wa (syn_wfun (syn_cres F A)) (syn_wss A (syn_cdm F))) (syn_wfo (syn_cres F A) A (syn_cima F A)) p0001 p0009
  exact p0010

noncomputable def g_foco
    (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfo F B C) (syn_wfo G A B)) (syn_wfo (syn_ccom F G) A C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fco A B C F G
  have p0001 :=
    @g_ad2ant2r (syn_wf F B C) (syn_wf G A B) (syn_wf (syn_ccom F G) A C) (.classEq (syn_crn F) C) (.classEq (syn_crn G) B) p0000
  have p0002 :=
    @g_fdm B C F
  have p0003 :=
    @g_eqtr3 (syn_cdm F) (syn_crn G) B
  have p0004 :=
    @g_sylan (syn_wf F B C) (.classEq (syn_cdm F) B) (.classEq (syn_crn G) B) (.classEq (syn_cdm F) (syn_crn G)) p0002 p0003
  have p0005 :=
    @g_rncoeq F G
  have p0006 :=
    @g_eqeq1d (.classEq (syn_cdm F) (syn_crn G)) (syn_crn (syn_ccom F G)) (syn_crn F) C p0005
  have p0007 :=
    @g_biimpar (.classEq (syn_cdm F) (syn_crn G)) (.classEq (syn_crn (syn_ccom F G)) C) (.classEq (syn_crn F) C) p0006
  have p0008 :=
    @g_sylan (syn_wa (syn_wf F B C) (.classEq (syn_crn G) B)) (.classEq (syn_cdm F) (syn_crn G)) (.classEq (syn_crn F) C) (.classEq (syn_crn (syn_ccom F G)) C) p0004 p0007
  have p0009 :=
    @g_an32s (syn_wf F B C) (.classEq (syn_crn G) B) (.classEq (syn_crn F) C) (.classEq (syn_crn (syn_ccom F G)) C) p0008
  have p0010 :=
    @g_adantrl (syn_wa (syn_wf F B C) (.classEq (syn_crn F) C)) (.classEq (syn_crn G) B) (.classEq (syn_crn (syn_ccom F G)) C) (syn_wf G A B) p0009
  have p0011 :=
    @g_jca (syn_wa (syn_wa (syn_wf F B C) (.classEq (syn_crn F) C)) (syn_wa (syn_wf G A B) (.classEq (syn_crn G) B))) (syn_wf (syn_ccom F G) A C) (.classEq (syn_crn (syn_ccom F G)) C) p0001 p0010
  have p0012 :=
    @g_dffo2 B C F
  have p0013 :=
    @g_dffo2 A B G
  have p0014 :=
    @g_anbi12i (syn_wfo F B C) (syn_wa (syn_wf F B C) (.classEq (syn_crn F) C)) (syn_wfo G A B) (syn_wa (syn_wf G A B) (.classEq (syn_crn G) B)) p0012 p0013
  have p0015 :=
    @g_dffo2 A C (syn_ccom F G)
  have p0016 :=
    @g_n_3imtr4i (syn_wa (syn_wa (syn_wf F B C) (.classEq (syn_crn F) C)) (syn_wa (syn_wf G A B) (.classEq (syn_crn G) B))) (syn_wa (syn_wf (syn_ccom F G) A C) (.classEq (syn_crn (syn_ccom F G)) C)) (syn_wa (syn_wfo F B C) (syn_wfo G A B)) (syn_wfo (syn_ccom F G) A C) p0011 p0014 p0015
  exact p0016

noncomputable def g_f1oeq1
    (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wf1o F A B) (syn_wf1o G A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_f1eq1 A B F G
  have p0001 :=
    @g_foeq1 A B F G
  have p0002 :=
    @g_anbi12d (.classEq F G) (syn_wf1 F A B) (syn_wf1 G A B) (syn_wfo F A B) (syn_wfo G A B) p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F A B)))
  have p0004 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o G A B)))
  have p0005 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wf1 F A B) (syn_wfo F A B)) (syn_wa (syn_wf1 G A B) (syn_wfo G A B)) (syn_wf1o F A B) (syn_wf1o G A B) p0002 p0003 p0004
  exact p0005

noncomputable def g_f1oeq2
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf1o F A C) (syn_wf1o F B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_f1eq2 A B C F
  have p0001 :=
    @g_foeq2 A B C F
  have p0002 :=
    @g_anbi12d (.classEq A B) (syn_wf1 F A C) (syn_wf1 F B C) (syn_wfo F A C) (syn_wfo F B C) p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F A C)))
  have p0004 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F B C)))
  have p0005 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wf1 F A C) (syn_wfo F A C)) (syn_wa (syn_wf1 F B C) (syn_wfo F B C)) (syn_wf1o F A C) (syn_wf1o F B C) p0002 p0003 p0004
  exact p0005

#print axioms g_f1oeq2

end NFChoice.DirectNominalPrf.WPPReplay
