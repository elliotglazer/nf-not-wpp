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
import NominalWPPReplayChunk009StructuralPart053


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

noncomputable def g_tfinrelkex
     :
    Nominal.NPrf (.classMem (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_snex (syn_csn (syn_c0))
  have p0001 :=
    @g_snex (syn_c0)
  have p0002 :=
    @g_xpkex (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)) p0000 p0001
  have p0003 :=
    @g_ssetkex
  have p0004 :=
    @g_ins2kex (syn_cssetk) p0003
  have p0005 :=
    @g_ssetkex
  have p0006 :=
    @g_cnvkex (syn_cssetk) p0005
  have p0007 :=
    @g_ins3kex (syn_ccnvk (syn_cssetk)) p0006
  have p0008 :=
    @g_nncex
  have p0009 :=
    @g_vvex
  have p0010 :=
    @g_xpkex (syn_cnnc) (syn_cvv) p0008 p0009
  have p0011 :=
    @g_ssetkex
  have p0012 :=
    @g_sikex (syn_cssetk) p0011
  have p0013 :=
    @g_ins2kex (syn_csik (syn_cssetk)) p0012
  have p0014 :=
    @g_n_1cex
  have p0015 :=
    @g_pwex (syn_c1c) p0014
  have p0016 :=
    @g_vvex
  have p0017 :=
    @g_xpkex (syn_cpw (syn_c1c)) (syn_cvv) p0015 p0016
  have p0018 :=
    @g_ssetkex
  have p0019 :=
    @g_ins3kex (syn_cssetk) p0018
  have p0020 :=
    @g_symdifex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))) p0019 p0013
  have p0021 :=
    @g_n_1cex
  have p0022 :=
    @g_pw1ex (syn_c1c) p0021
  have p0023 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0022
  have p0024 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0023
  have p0025 :=
    @g_imakex (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0020 p0024
  have p0026 :=
    @g_difex (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0017 p0025
  have p0027 :=
    @g_sikex (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0026
  have p0028 :=
    @g_ins3kex (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0027
  have p0029 :=
    @g_inex (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)) p0028 p0004
  have p0030 :=
    @g_imakex (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0029 p0023
  have p0031 :=
    @g_ins3kex (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0030
  have p0032 :=
    @g_inex (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0013 p0031
  have p0033 :=
    @g_imakex (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0032 p0024
  have p0034 :=
    @g_inex (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0010 p0033
  have p0035 :=
    @g_ins2kex (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0034
  have p0036 :=
    @g_idkex
  have p0037 :=
    @g_ins3kex (syn_cidk) p0036
  have p0038 :=
    @g_symdifex (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)) p0035 p0037
  have p0039 :=
    @g_imakex (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)) p0038 p0022
  have p0040 :=
    @g_ins2kex (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))) p0039
  have p0041 :=
    @g_difex (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))) p0007 p0040
  have p0042 :=
    @g_imakex (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)) p0041 p0022
  have p0043 :=
    @g_ins3kex (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))) p0042
  have p0044 :=
    @g_symdifex (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))) p0004 p0043
  have p0045 :=
    @g_imakex (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0044 p0023
  have p0046 :=
    @g_complex (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0045
  have p0047 :=
    @g_vvex
  have p0048 :=
    @g_xpkex (syn_csn (syn_csn (syn_c0))) (syn_cvv) p0000 p0047
  have p0049 :=
    @g_difex (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)) p0046 p0048
  have p0050 :=
    @g_unex (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))) p0002 p0049
  exact p0050

noncomputable def g_tfineq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ctfin A) (syn_ctfin B))) := by
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
  have p0000 :=
    @g_eqeq1 A B (syn_c0)
  have p0001 :=
    @g_rexeq (.classMem (syn_cpw1 (.cv y)) (.cv x)) y A B (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0002 :=
    @g_anbi2d (.classEq A B) (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x))) (syn_wrex y B (.classMem (syn_cpw1 (.cv y)) (.cv x))) (.classMem (.cv x) (syn_cnnc)) p0001
  have p0003 :=
    @g_iotabidv (.classEq A B) (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y B (.classMem (syn_cpw1 (.cv y)) (.cv x)))) x (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0002
  have p0004 :=
    @g_ifbieq2d (.classEq A B) (.classEq A (syn_c0)) (.classEq B (syn_c0)) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x))))) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y B (.classMem (syn_cpw1 (.cv y)) (.cv x))))) (syn_c0) p0000 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin x A y (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (show y ≠ x from (by exact fresh_y_ne_x))
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin x B y (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (show y ≠ x from (by exact fresh_y_ne_x))
  have p0007 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cif (.classEq A (syn_c0)) (syn_c0) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x)))))) (syn_cif (.classEq B (syn_c0)) (syn_c0) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y B (.classMem (syn_cpw1 (.cv y)) (.cv x)))))) (syn_ctfin A) (syn_ctfin B) p0004 p0005 p0006
  exact p0007

noncomputable def g_tfinprop
    (M : Class) (a : Var) (dv_M_a : a ∉ M.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))))) := by
  let proofSupport : Finset Var := M.fv ∪ ({a} : Finset Var)
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_n : a ≠ n :=
    Ne.symm fresh_n_ne_a
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin n M a (by exact (show a ∉ (M).fv from (by exact dv_M_a))) (by exact (show n ∉ (M).fv from (by exact fresh_n_not_M))) (show a ≠ n from (by exact fresh_a_ne_n))
  have p0001 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne M (syn_c0))))
  have p0002 :=
    @g_iffalse (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
  have p0003 :=
    @g_sylbi (syn_wne M (syn_c0)) (.neg (.classEq M (syn_c0))) (.classEq (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))) p0001 p0002
  have p0004 :=
    @g_adantl (syn_wne M (syn_c0)) (.classEq (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))) (.classMem M (syn_cnnc)) p0003
  have p0005 :=
    @g_nnpw1ex n M a (by exact (show a ∉ (M).fv from (by exact dv_M_a))) (by exact (show n ∉ (M).fv from (by exact fresh_n_not_M))) (show a ≠ n from (by exact fresh_a_ne_n))
  have p0006 :=
    @g_reiotacl (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) n (syn_cnnc) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0007 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))) (.classMem (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) (syn_cnnc)) p0005 p0006
  have p0008 :=
    @g_eqeltrd (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) (syn_cnnc) p0004 p0007
  have p0009 :=
    @g_syl5eqel (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_ctfin M) (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))) (syn_cnnc) p0000 p0008
  have p0010 :=
    @g_syl5req (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_ctfin M) (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) p0000 p0004
  have p0011 :=
    @g_jca (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))) p0009 p0005
  have p0012 :=
    @g_eleq2 (.cv n) (syn_ctfin M) (syn_cpw1 (.cv a))
  have p0013 :=
    @g_rexbidv (.classEq (.cv n) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) a M (by exact (show a ∉ ((Wff.classEq (.cv n) (syn_ctfin M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((Class.cv n)).fv) ∪ (((syn_ctfin M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ n from (by exact fresh_a_ne_n)))))) (show a ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show a ∉ (M).fv from (by exact dv_M_a))))))))) p0012
  have p0014 :=
    @g_reiota2 (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))) n (syn_cnnc) (syn_ctfin M) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show n ∉ (M).fv from (by exact fresh_n_not_M))))) (by exact (show n ∉ ((syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show n ∉ (((M).fv).erase a) ∪ ((((Wff.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))).fv).erase a) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((M).fv).erase a from (fun hmem => (show n ∉ (M).fv from (by exact fresh_n_not_M)) (Finset.mem_of_mem_erase hmem))) (show n ∉ (((Wff.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))).fv).erase a from (fun hmem => (show n ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_ctfin M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show n ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ a from (by exact fresh_n_ne_a)))))))) (show n ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show n ∉ (M).fv from (by exact fresh_n_not_M)))))))) (Finset.mem_of_mem_erase hmem)))))))) p0013
  have p0015 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) (syn_wb (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))) (.classEq (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) (syn_ctfin M))) p0011 p0014
  have p0016 :=
    @g_mpbird (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))) (.classEq (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) (syn_ctfin M)) p0010 p0015
  have p0017 :=
    @g_jca (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))) p0009 p0016
  exact p0017

noncomputable def g_tfinnnul
    (M : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wne (syn_ctfin M) (syn_c0))) := by
  let proofSupport : Finset Var := M.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    @g_tfinprop M x (by exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))
  have p0001 :=
    @g_ne0i (syn_ctfin M) (syn_cpw1 (.cv x))
  have p0002 :=
    @g_rexlimivw (.classMem (syn_cpw1 (.cv x)) (syn_ctfin M)) (syn_wne (syn_ctfin M) (syn_c0)) x M (by exact (show x ∉ ((syn_wne (syn_ctfin M) (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show x ∉ (((syn_ctfin M)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))) (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0001
  have p0003 :=
    @g_adantl (syn_wrex x M (.classMem (syn_cpw1 (.cv x)) (syn_ctfin M))) (syn_wne (syn_ctfin M) (syn_c0)) (.classMem (syn_ctfin M) (syn_cnnc)) p0002
  have p0004 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (syn_wrex x M (.classMem (syn_cpw1 (.cv x)) (syn_ctfin M)))) (syn_wne (syn_ctfin M) (syn_c0)) p0000 p0003
  exact p0004

noncomputable def g_tfinnul
     :
    Nominal.NPrf (.classEq (syn_ctfin (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin x (syn_c0) y (by exact (show y ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (show y ≠ x from (by exact fresh_y_ne_x))
  have p0001 :=
    @g_eqid (syn_c0)
  have p0002 :=
    @g_iftrue (.classEq (syn_c0) (syn_c0)) (syn_c0) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y (syn_c0) (.classMem (syn_cpw1 (.cv y)) (.cv x)))))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_eqtri (syn_ctfin (syn_c0)) (syn_cif (.classEq (syn_c0) (syn_c0)) (syn_c0) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y (syn_c0) (.classMem (syn_cpw1 (.cv y)) (.cv x)))))) (syn_c0) p0000 p0003
  exact p0004

noncomputable def g_tfincl
    (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc))) := by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have p0000 :=
    @g_tfinnul
  have p0001 :=
    @g_tfineq N (syn_c0)
  have p0002 :=
    @g_id (.classEq N (syn_c0))
  have p0003 :=
    @g_n_3eqtr4a (.classEq N (syn_c0)) (syn_ctfin (syn_c0)) (syn_c0) (syn_ctfin N) N p0000 p0001 p0002
  have p0004 :=
    @g_eleq1d (.classEq N (syn_c0)) (syn_ctfin N) N (syn_cnnc) p0003
  have p0005 :=
    @g_biimprd (.classEq N (syn_c0)) (.classMem (syn_ctfin N) (syn_cnnc)) (.classMem N (syn_cnnc)) p0004
  have p0006 :=
    @g_tfinprop N a (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
  have p0007 :=
    @g_simpld (syn_wa (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))) (.classMem (syn_ctfin N) (syn_cnnc)) (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) p0006
  have p0008 :=
    @g_expcom (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) (.classMem (syn_ctfin N) (syn_cnnc)) p0007
  have p0009 :=
    @g_pm2_61ine (.imp (.classMem N (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc))) N (syn_c0) p0005 p0008
  exact p0009



#print axioms g_tfincl

end NFChoice.DirectNominalPrf.WPPReplay
