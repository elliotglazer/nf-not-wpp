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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk009StructuralPart022


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

noncomputable def g_addcexlem
     :
    Nominal.NPrf (.classMem (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_ssetkex
  have p0001 :=
    @g_ins3kex (syn_cssetk) p0000
  have p0002 :=
    @g_ssetkex
  have p0003 :=
    @g_ins2kex (syn_cssetk) p0002
  have p0004 :=
    @g_inex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)) p0001 p0003
  have p0005 :=
    @g_n_1cex
  have p0006 :=
    @g_pw1ex (syn_c1c) p0005
  have p0007 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0006
  have p0008 :=
    @g_imakex (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0004 p0007
  have p0009 :=
    @g_complex (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0008
  have p0010 :=
    @g_ins3kex (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0009
  have p0011 :=
    @g_ins2kex (syn_cins2k (syn_cssetk)) p0003
  have p0012 :=
    @g_ins2kex (syn_cins3k (syn_cssetk)) p0001
  have p0013 :=
    @g_ssetkex
  have p0014 :=
    @g_sikex (syn_cssetk) p0013
  have p0015 :=
    @g_sikex (syn_csik (syn_cssetk)) p0014
  have p0016 :=
    @g_ins3kex (syn_csik (syn_csik (syn_cssetk))) p0015
  have p0017 :=
    @g_unex (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) p0012 p0016
  have p0018 :=
    @g_symdifex (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))) p0011 p0017
  have p0019 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0007
  have p0020 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0019
  have p0021 :=
    @g_imakex (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0018 p0020
  have p0022 :=
    @g_difex (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0010 p0021
  exact p0022

noncomputable def g_addceq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cplc A C) (syn_cplc B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_imakeq2 A B (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 C)))
  have p0001 :=
    @g_dfaddc2 A C
  have p0002 :=
    @g_dfaddc2 B C
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 C))) A) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 C))) B) (syn_cplc A C) (syn_cplc B C) p0000 p0001 p0002
  exact p0003

noncomputable def g_addceq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cplc C A) (syn_cplc C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_pw1eq A B
  have p0001 :=
    @g_pw1eq (syn_cpw1 A) (syn_cpw1 B)
  have p0002 :=
    @g_syl (.classEq A B) (.classEq (syn_cpw1 A) (syn_cpw1 B)) (.classEq (syn_cpw1 (syn_cpw1 A)) (syn_cpw1 (syn_cpw1 B))) p0000 p0001
  have p0003 :=
    @g_imakeq2d (.classEq A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw1 (syn_cpw1 B)) (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0002
  have p0004 :=
    @g_imakeq1d (.classEq A B) (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 A))) (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))) C p0003
  have p0005 :=
    @g_dfaddc2 C A
  have p0006 :=
    @g_dfaddc2 C B
  have p0007 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 A))) C) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))) C) (syn_cplc C A) (syn_cplc C B) p0004 p0005 p0006
  exact p0007

noncomputable def g_addceq12
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq A C) (.classEq B D)) (.classEq (syn_cplc A B) (syn_cplc C D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_addceq1 A C B
  have p0001 :=
    @g_addceq2 B D C
  have p0002 :=
    @g_sylan9eq (.classEq A C) (.classEq B D) (syn_cplc A B) (syn_cplc C B) (syn_cplc C D) p0000 p0001
  exact p0002

noncomputable def g_addceq1i
    (A : Class) (B : Class) (C : Class) (hyp_addceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cplc A C) (syn_cplc B C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_addceq1 A B C
  have p0001 :=
    Nominal.mp hyp_addceqi_1 p0000
  exact p0001

noncomputable def g_addceq2i
    (A : Class) (B : Class) (C : Class) (hyp_addceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cplc C A) (syn_cplc C B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_addceq2 A B C
  have p0001 :=
    Nominal.mp hyp_addceqi_1 p0000
  exact p0001

noncomputable def g_addceq12i
    (A : Class) (B : Class) (C : Class) (D : Class) (hyp_addceqi_1 : Nominal.NPrf (.classEq A B)) (hyp_addceqi_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cplc A C) (syn_cplc B D)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_addceq12 A C B D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (.classEq (syn_cplc A C) (syn_cplc B D)) hyp_addceqi_1 hyp_addceqi_2 p0000
  exact p0001

noncomputable def g_addceq1d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_addceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cplc A C) (syn_cplc B C))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_addceq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cplc A C) (syn_cplc B C)) hyp_addceqd_1 p0000
  exact p0001

noncomputable def g_addceq2d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_addceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cplc C A) (syn_cplc C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_addceq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cplc C A) (syn_cplc C B)) hyp_addceqd_1 p0000
  exact p0001

noncomputable def g_addceq12d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (hyp_addceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) (hyp_addceqd_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cplc A C) (syn_cplc B D))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_addceq12 A C B D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (.classEq (syn_cplc A C) (syn_cplc B D)) hyp_addceqd_1 hyp_addceqd_2 p0000
  exact p0001

noncomputable def g_n_0cex
     :
    Nominal.NPrf (.classMem (syn_c0c) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_c0c] using (Nominal.classEqRefl (syn_c0c)))
  have p0001 :=
    @g_snex (syn_c0)
  have p0002 :=
    @g_eqeltri (syn_c0c) (syn_csn (syn_c0)) (syn_cvv) p0000 p0001
  exact p0002

noncomputable def g_addcexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cplc A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_dfaddc2 A B
  have p0001 :=
    @g_pw1exg B W
  have p0002 :=
    @g_pw1exg (syn_cpw1 B) (syn_cvv)
  have p0003 :=
    @g_addcexlem
  have p0004 :=
    @g_imakexg (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_mpan (.classMem (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cvv)) (.classMem (syn_cpw1 (syn_cpw1 B)) (syn_cvv)) (.classMem (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_n_3syl (.classMem B W) (.classMem (syn_cpw1 B) (syn_cvv)) (.classMem (syn_cpw1 (syn_cpw1 B)) (syn_cvv)) (.classMem (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))) (syn_cvv)) p0001 p0002 p0005
  have p0007 :=
    @g_imakexg (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))) A (syn_cvv) V
  have p0008 :=
    @g_sylan (.classMem B W) (.classMem (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))) (syn_cvv)) (.classMem A V) (.classMem (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))) A) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_ancoms (.classMem B W) (.classMem A V) (.classMem (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))) A) (syn_cvv)) p0008
  have p0010 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cplc A B) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))) A) (syn_cvv) p0000 p0009
  exact p0010

noncomputable def g_addcex
    (A : Class) (B : Class) (hyp_addcex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_addcex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cplc A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_addcexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cplc A B) (syn_cvv)) hyp_addcex_1 hyp_addcex_2 p0000
  exact p0001



#print axioms g_addcex

end NFChoice.DirectNominalPrf.WPPReplay
