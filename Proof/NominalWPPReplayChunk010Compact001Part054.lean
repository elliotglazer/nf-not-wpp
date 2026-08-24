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
import NominalWPPReplayChunk010Compact001Part053

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

noncomputable def g_imaexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cima A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_dfima2 A B
  have p0001 :=
    @g_pw1exg A V
  have p0002 :=
    @g_pw1exg (syn_cpw1 A) (syn_cvv)
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_vvex
  have p0005 :=
    @g_vvex
  have p0006 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0004 p0005
  have p0007 :=
    @g_xpkex (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_setconslem5
  have p0009 :=
    @g_inex (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0007 p0008
  have p0010 :=
    @g_imakexg (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A)) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_mpan (.classMem (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cvv)) (.classMem (syn_cpw1 (syn_cpw1 A)) (syn_cvv)) (.classMem (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_n_3syl (.classMem A V) (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem (syn_cpw1 (syn_cpw1 A)) (syn_cvv)) (.classMem (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) (syn_cvv)) p0001 p0002 p0011
  have p0013 :=
    @g_imakexg (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) B (syn_cvv) W
  have p0014 :=
    @g_sylan (.classMem A V) (.classMem (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) (syn_cvv)) (.classMem B W) (.classMem (syn_cimak (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) B) (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cima A B) (syn_cimak (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) B) (syn_cvv) p0000 p0014
  exact p0015

noncomputable def g_imaex
    (A : Class) (B : Class) (hyp_imaex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_imaex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cima A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_imaexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cima A B) (syn_cvv)) hyp_imaex_1 hyp_imaex_2 p0000
  exact p0001

#print axioms g_imaex

end NFChoice.DirectNominalPrf.WPPReplay
