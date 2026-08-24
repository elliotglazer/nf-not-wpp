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
import NominalWPPReplayChunk015Compact001Part031

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

noncomputable def g_wpppostcompfv
    (R : Class) (F : Class) (hyp_wpppostcompfv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wpppostcompfv_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpppostcomp F) R) (syn_ccom F R)) := by
  let proofSupport : Finset Var := R.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpppostcomp] using (Nominal.classEqRefl (syn_cwpppostcomp F)))
  have p0001 :=
    @g_fveq1i R (syn_cwpppostcomp F) (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) p0000
  have p0002 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0003 :=
    Nominal.mp hyp_wpppostcompfv_1 p0002
  have p0004 :=
    @g_f1ovi
  have p0005 :=
    @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_inidm (syn_cvv)
  have p0011 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) p0010
  have p0012 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) (syn_cvv)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) (syn_cvv)) (.classMem R (syn_cvv)) p0012 hyp_wpppostcompfv_2
  have p0014 :=
    @g_fvco2 (syn_cvv) R (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0017 :=
    Nominal.mp hyp_wpppostcompfv_1 p0016
  have p0018 :=
    @g_f1ovi
  have p0019 :=
    @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_fvtxpvv R (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid) p0017 p0020 hyp_wpppostcompfv_2
  have p0022 :=
    @g_fvconst2 (syn_cvv) F R hyp_wpppostcompfv_1
  have p0023 :=
    Nominal.mp hyp_wpppostcompfv_2 p0022
  have p0024 :=
    @g_fvi R (syn_cvv)
  have p0025 :=
    Nominal.mp hyp_wpppostcompfv_2 p0024
  have p0026 :=
    @g_opeq12i (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) R) F (syn_cfv (syn_cid) R) R p0023 p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) R) (syn_cop (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) R) (syn_cfv (syn_cid) R)) (syn_cop F R) p0021 p0026
  have p0028 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) R) (syn_cop F R) (syn_ccompose) p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) R) (syn_cfv (syn_ccompose) (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) R)) (syn_cfv (syn_ccompose) (syn_cop F R)) p0015 p0028
  have p0030 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co F (syn_ccompose) R)))
  have p0031 :=
    @g_eqcomi (syn_co F (syn_ccompose) R) (syn_cfv (syn_ccompose) (syn_cop F R)) p0030
  have p0032 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) R) (syn_cfv (syn_ccompose) (syn_cop F R)) (syn_co F (syn_ccompose) R) p0029 p0031
  have p0033 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem R (syn_cvv)) hyp_wpppostcompfv_1 hyp_wpppostcompfv_2
  have p0034 :=
    @g_composevalg F R (syn_cvv) (syn_cvv)
  have p0035 :=
    Nominal.mp p0033 p0034
  have p0036 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) R) (syn_co F (syn_ccompose) R) (syn_ccom F R) p0032 p0035
  have p0037 :=
    @g_eqtri (syn_cfv (syn_cwpppostcomp F) R) (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) R) (syn_ccom F R) p0001 p0036
  exact p0037

noncomputable def g_wppupperpreopfn
    (C : Class) :
    Nominal.NPrf (syn_wfn (syn_cwppupperpreop C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv
  have p0000 :=
    @g_lnimageopfn
  have p0001 :=
    @g_imageswapfn
  have p0002 :=
    @g_wppreachupperex C
  have p0003 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_inidm (syn_cvv)
  have p0009 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) p0008
  have p0010 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) (syn_cvv)) p0007 p0009
  have p0011 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) p0000 p0010
  have p0012 :=
    (by simpa [syn_cwppupperpreop] using (Nominal.classEqRefl (syn_cwppupperpreop C)))
  have p0013 :=
    @g_fneq1i (syn_cvv) (syn_cwppupperpreop C) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) p0012
  have p0014 :=
    @g_mpbir (syn_wfn (syn_cwppupperpreop C) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) (syn_cvv)) p0011 p0013
  exact p0014

noncomputable def g_wppimageswapfv
    (R : Class) (hyp_wppimageswapfv_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R)) := by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have dv_cache_0001 : x ∉ (R).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv x) R)
  have p0001 :=
    @g_fveq2d (.classEq (.cv x) R) (.cv x) R (syn_cimage (syn_cswap)) p0000
  have p0002 :=
    @g_id (.classEq (.cv x) R)
  have p0003 :=
    @g_cnveqd (.classEq (.cv x) R) (.cv x) R p0002
  have p0004 :=
    @g_eqeq12d (.classEq (.cv x) R) (syn_cfv (syn_cimage (syn_cswap)) (.cv x)) (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv (.cv x)) (syn_ccnv R) p0001 p0003
  have p0005 :=
    @g_imageswapval x
  have p0006 :=
    @g_vtoclg (.classEq (syn_cfv (syn_cimage (syn_cswap)) (.cv x)) (syn_ccnv (.cv x))) (.classEq (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R)) x R (syn_cvv) dv_cache_0001 dv_cache_0002 p0004 p0005
  have p0007 :=
    Nominal.mp hyp_wppimageswapfv_1 p0006
  exact p0007

noncomputable def g_wppupperpreopfv
    (C : Class) (R : Class) (hyp_wppupperpreopfv_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppupperpreop C) R) (syn_cima (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C)))) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cwppupperpreop] using (Nominal.classEqRefl (syn_cwppupperpreop C)))
  have p0001 :=
    @g_fveq1i R (syn_cwppupperpreop C) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) p0000
  have p0002 :=
    @g_imageswapfn
  have p0003 :=
    @g_wppreachupperex C
  have p0004 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_inidm (syn_cvv)
  have p0010 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) p0009
  have p0011 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) (syn_cvv)) (.classMem R (syn_cvv)) p0011 hyp_wppupperpreopfv_1
  have p0013 :=
    @g_fvco2 (syn_cvv) R (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_imageswapfn
  have p0016 :=
    @g_wppreachupperex C
  have p0017 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_fvtxpvv R (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) p0015 p0018 hyp_wppupperpreopfv_1
  have p0020 :=
    @g_wppimageswapfv R hyp_wppupperpreopfv_1
  have p0021 :=
    @g_wppreachupperex C
  have p0022 :=
    @g_fvconst2 (syn_cvv) (syn_cima (syn_clec) (syn_csn C)) R p0021
  have p0023 :=
    Nominal.mp hyp_wppupperpreopfv_1 p0022
  have p0024 :=
    @g_opeq12i (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R) (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) R) (syn_cima (syn_clec) (syn_csn C)) p0020 p0023
  have p0025 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) R) (syn_cop (syn_cfv (syn_cimage (syn_cswap)) R) (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) R)) (syn_cop (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))) p0019 p0024
  have p0026 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) R) (syn_cop (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))) (syn_clnimageop) p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) R) (syn_cfv (syn_clnimageop) (syn_cfv (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) R)) (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C)))) p0014 p0026
  have p0028 :=
    @g_cnvex R hyp_wppupperpreopfv_1
  have p0029 :=
    @g_wppreachupperex C
  have p0030 :=
    @g_lnimageopval (syn_cima (syn_clec) (syn_csn C)) (syn_ccnv R) p0028 p0029
  have p0031 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) R) (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C)))) (syn_cima (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))) p0027 p0030
  have p0032 :=
    @g_eqtri (syn_cfv (syn_cwppupperpreop C) R) (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) R) (syn_cima (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))) p0001 p0031
  exact p0032

noncomputable def g_wpppowlayerseqfun
    (C : Class) (F : Class) (hyp_wpppowlayerseqfun_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfun (syn_cwpppowlayerseq F C)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_wppupperpreopfn C
  have p0001 :=
    @g_fnfun (syn_cvv) (syn_cwppupperpreop C)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_wpppostcompfn F hyp_wpppowlayerseqfun_1
  have p0004 :=
    @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_wpppostcompex F hyp_wpppowlayerseqfun_1
  have p0007 :=
    @g_elfuns (syn_cwpppostcomp F) p0006
  have p0008 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F)) p0005 p0007
  have p0009 :=
    @g_idex
  have p0010 :=
    @g_wpppostcompfn F hyp_wpppowlayerseqfun_1
  have p0011 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0009 p0012
  have p0014 :=
    @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0015 :=
    @g_wpppostcompfn F hyp_wpppowlayerseqfun_1
  have p0016 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0014 p0017
  have p0019 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F))) (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0008 p0013 p0018
  have p0020 :=
    @g_wpporbitfnndv (syn_cwpppostcomp F) (syn_cid)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_fnfun (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_fntcfn
  have p0025 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_pm3_2i (syn_wfun (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_wfun (syn_ctcfn)) p0023 p0026
  have p0028 :=
    @g_funco (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_pm3_2i (syn_wfun (syn_cwppupperpreop C)) (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) p0002 p0029
  have p0031 :=
    @g_funco (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    (by simpa [syn_cwpppowlayerseq] using (Nominal.classEqRefl (syn_cwpppowlayerseq F C)))
  have p0034 :=
    @g_funeqi (syn_cwpppowlayerseq F C) (syn_ccom (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) p0033
  have p0035 :=
    @g_mpbir (syn_wfun (syn_cwpppowlayerseq F C)) (syn_wfun (syn_ccom (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) p0032 p0034
  exact p0035

noncomputable def g_wpphitfamfv
    (C : Class) (D : Class) (F : Class) (hyp_wpphitfamfv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D))) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (syn_cima (syn_csset) (syn_csn (syn_csn D))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpphitfam] using (Nominal.classEqRefl (syn_cwpphitfam F C)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn D)) (syn_cwpphitfam F C) (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset))) p0000
  have p0002 :=
    @g_wppimagefun (syn_csset)
  have p0003 :=
    @g_eqid (syn_cima (syn_csset) (syn_csn (syn_csn D)))
  have p0004 :=
    @g_snex (syn_csn D)
  have p0005 :=
    @g_ssetex
  have p0006 :=
    @g_snex (syn_csn D)
  have p0007 :=
    @g_imaex (syn_csset) (syn_csn (syn_csn D)) p0005 p0006
  have p0008 :=
    @g_brimage (syn_csn (syn_csn D)) (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_csset) p0004 p0007
  have p0009 :=
    @g_mpbir (syn_wbr (syn_csn (syn_csn D)) (syn_cimage (syn_csset)) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (.classEq (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) p0003 p0008
  have p0010 :=
    @g_breldm (syn_csn (syn_csn D)) (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_cimage (syn_csset))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_pm3_2i (syn_wfun (syn_cimage (syn_csset))) (.classMem (syn_csn (syn_csn D)) (syn_cdm (syn_cimage (syn_csset)))) p0002 p0011
  have p0013 :=
    @g_fvco (syn_csn (syn_csn D)) (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D))) (syn_cfv (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset))) (syn_csn (syn_csn D))) (syn_cfv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D)))) p0001 p0014
  have p0016 :=
    @g_ssetex
  have p0017 :=
    @g_snex (syn_csn D)
  have p0018 :=
    @g_wppimagefv (syn_csn (syn_csn D)) (syn_csset) p0016 p0017
  have p0019 :=
    @g_fveq2i (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D))) (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) p0018
  have p0020 :=
    @g_eqtri (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D))) (syn_cfv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D)))) (syn_cfv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) p0015 p0019
  have p0021 :=
    @g_wpppowlayerseqex C F hyp_wpphitfamfv_1
  have p0022 :=
    @g_cnvex (syn_cwpppowlayerseq F C) p0021
  have p0023 :=
    @g_ssetex
  have p0024 :=
    @g_snex (syn_csn D)
  have p0025 :=
    @g_imaex (syn_csset) (syn_csn (syn_csn D)) p0023 p0024
  have p0026 :=
    @g_wppimagefv (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_ccnv (syn_cwpppowlayerseq F C)) p0022 p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D))) (syn_cfv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) p0020 p0026
  exact p0027

noncomputable def g_elwpphitfam
    (C : Class) (D : Class) (F : Class) (q : Var) (hyp_elwpphitfam_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_elwpphitfam_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D)))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv ∪ ({q} : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_q : y ≠ q := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_q : z ≠ q := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classMem D (.cv z))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cima (syn_csset) (syn_csn (syn_csn D)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cab y (.classMem D (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, fresh_y_not_C, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_ne_q, fresh_y_not_C, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wpphitfamfv C D F hyp_elwpphitfam_1
  have p0001 :=
    @g_eleq2i (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D))) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (syn_csn (.cv q)) p0000
  have p0002 :=
    @g_elimasn (syn_csset) (syn_csn D) (.cv z)
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn D) (syn_csset) (.cv z))))
  have p0004 :=
    @g_bicomi (syn_wbr (syn_csn D) (syn_csset) (.cv z)) (.classMem (syn_cop (syn_csn D) (.cv z)) (syn_csset)) p0003
  have p0005 :=
    @g_bitri (.classMem (.cv z) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (.classMem (syn_cop (syn_csn D) (.cv z)) (syn_csset)) (syn_wbr (syn_csn D) (syn_csset) (.cv z)) p0002 p0004
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_brssetsn D (.cv z) hyp_elwpphitfam_2 p0006
  have p0008 :=
    @g_bitri (.classMem (.cv z) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (syn_wbr (syn_csn D) (syn_csset) (.cv z)) (.classMem D (.cv z)) p0005 p0007
  have p0009 :=
    @g_vex z
  have p0010 :=
    @g_id (.classEq (.cv y) (.cv z))
  have p0011 :=
    @g_eleq2d (.classEq (.cv y) (.cv z)) (.cv y) (.cv z) D p0010
  have p0012 :=
    @g_elab (.classMem D (.cv y)) (.classMem D (.cv z)) y (.cv z) dv_cache_0001 dv_cache_0002 p0009 p0011
  have p0013 :=
    @g_bitr4i (.classMem (.cv z) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (.classMem D (.cv z)) (.classMem (.cv z) (.cab y (.classMem D (.cv y)))) p0008 p0012
  have p0014 :=
    @g_eqriv z (syn_cima (syn_csset) (syn_csn (syn_csn D))) (.cab y (.classMem D (.cv y))) dv_cache_0003 dv_cache_0004 p0013
  have p0015 :=
    @g_imaeq2i (syn_cima (syn_csset) (syn_csn (syn_csn D))) (.cab y (.classMem D (.cv y))) (syn_ccnv (syn_cwpppowlayerseq F C)) p0014
  have p0016 :=
    @g_eleq2i (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y)))) (syn_csn (.cv q)) p0015
  have p0017 :=
    @g_bitri (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D)))) (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (syn_cima (syn_csset) (syn_csn (syn_csn D))))) (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y))))) p0001 p0016
  have p0018 :=
    @g_wpppowlayerseqfun C F hyp_elwpphitfam_1
  have p0019 :=
    @g_funfn (syn_cwpppowlayerseq F C)
  have p0020 :=
    @g_mpbi (syn_wfun (syn_cwpppowlayerseq F C)) (syn_wfn (syn_cwpppowlayerseq F C) (syn_cdm (syn_cwpppowlayerseq F C))) p0018 p0019
  have p0021 :=
    @g_elpreima (syn_cdm (syn_cwpppowlayerseq F C)) (syn_csn (.cv q)) (.cab y (.classMem D (.cv y))) (syn_cwpppowlayerseq F C)
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_fvex (syn_csn (.cv q)) (syn_cwpppowlayerseq F C)
  have p0024 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))))
  have p0025 :=
    @g_eleq2d (.classEq (.cv y) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) (.cv y) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) D p0024
  have p0026 :=
    @g_elab (.classMem D (.cv y)) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) y (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) dv_cache_0005 dv_cache_0006 p0023 p0025
  have p0027 :=
    @g_elfvdm D (syn_csn (.cv q)) (syn_cwpppowlayerseq F C)
  have p0028 :=
    @g_sylbi (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) (.classMem (syn_csn (.cv q)) (syn_cdm (syn_cwpppowlayerseq F C))) p0026 p0027
  have p0029 :=
    @g_pm4_71ri (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) (.classMem (syn_csn (.cv q)) (syn_cdm (syn_cwpppowlayerseq F C))) p0028
  have p0030 :=
    @g_bicomi (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) (syn_wa (.classMem (syn_csn (.cv q)) (syn_cdm (syn_cwpppowlayerseq F C))) (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y))))) p0029
  have p0031 :=
    @g_bitri (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y))))) (syn_wa (.classMem (syn_csn (.cv q)) (syn_cdm (syn_cwpppowlayerseq F C))) (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y))))) (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) p0022 p0030
  have p0032 :=
    @g_fvex (syn_csn (.cv q)) (syn_cwpppowlayerseq F C)
  have p0033 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))))
  have p0034 :=
    @g_eleq2d (.classEq (.cv y) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) (.cv y) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) D p0033
  have p0035 :=
    @g_elab (.classMem D (.cv y)) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) y (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) dv_cache_0005 dv_cache_0006 p0032 p0034
  have p0036 :=
    @g_bitri (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y))))) (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) p0031 p0035
  have p0037 :=
    @g_bitri (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D)))) (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y))))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) p0017 p0036
  exact p0037

noncomputable def g_wpppredmemrelex
    (C : Class) (F : Class) (hyp_wpppredmemrelex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppredmemrel F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpppredmemrel] using (Nominal.classEqRefl (syn_cwpppredmemrel F C)))
  have p0001 :=
    @g_ssetex
  have p0002 :=
    @g_cnvex (syn_csset) p0001
  have p0003 :=
    @g_wpppredfamex C F hyp_wpppredmemrelex_1
  have p0004 :=
    @g_coex (syn_ccnv (syn_csset)) (syn_cwpppredfam F C) p0002 p0003
  have p0005 :=
    @g_eqeltri (syn_cwpppredmemrel F C) (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpppredfam F C)) (syn_cvv) p0000 p0004
  exact p0005

noncomputable def g_wpphitmemrelex
    (C : Class) (F : Class) (hyp_wpppredmemrelex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpphitmemrel F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpphitmemrel] using (Nominal.classEqRefl (syn_cwpphitmemrel F C)))
  have p0001 :=
    @g_ssetex
  have p0002 :=
    @g_cnvex (syn_csset) p0001
  have p0003 :=
    @g_wpphitfamex C F hyp_wpppredmemrelex_1
  have p0004 :=
    @g_coex (syn_ccnv (syn_csset)) (syn_cwpphitfam F C) p0002 p0003
  have p0005 :=
    @g_eqeltri (syn_cwpphitmemrel F C) (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpphitfam F C)) (syn_cvv) p0000 p0004
  exact p0005

noncomputable def g_wppreachincbex
    (C : Class) (F : Class) (hyp_wppreachincbex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppreachincb F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwppreachincb] using (Nominal.classEqRefl (syn_cwppreachincb F C)))
  have p0001 :=
    @g_nncex
  have p0002 :=
    @g_pw1ex (syn_cnnc) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_cnnc)) p0002
  have p0004 :=
    @g_wpppredmemrelex C F hyp_wppreachincbex_1
  have p0005 :=
    @g_wpphitmemrelex C F hyp_wppreachincbex_1
  have p0006 :=
    @g_symdifex (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C) p0004 p0005
  have p0007 :=
    @g_dmex F hyp_wppreachincbex_1
  have p0008 :=
    @g_pw1ex (syn_cdm F) p0007
  have p0009 :=
    @g_pw1ex (syn_cpw1 (syn_cdm F)) p0008
  have p0010 :=
    @g_resex (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))) p0006 p0009
  have p0011 :=
    @g_rnex (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))) p0010
  have p0012 :=
    @g_difex (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))) p0003 p0011
  have p0013 :=
    @g_uni1ex (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))) p0012
  have p0014 :=
    @g_uni1ex (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) p0013
  have p0015 :=
    @g_eqeltri (syn_cwppreachincb F C) (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) (syn_cvv) p0000 p0014
  exact p0015

noncomputable def g_elwppreachincb
    (C : Class) (F : Class) (N : Class) (dv_C_F : Disjoint C.fv F.fv) (dv_C_N : Disjoint C.fv N.fv) (dv_F_N : Disjoint F.fv N.fv) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem N (syn_cwppreachincb F C)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ N.fv
  have p0000 :=
    (by simpa [syn_cwppreachincb] using (Nominal.classEqRefl (syn_cwppreachincb F C)))
  have p0001 :=
    @g_eleq2i (syn_cwppreachincb F C) (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) N p0000
  have p0002 :=
    @g_a1i (syn_wb (.classMem N (syn_cwppreachincb F C)) (.classMem N (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))))) (.classMem N (syn_cnnc)) p0001
  have p0003 :=
    @g_eluni1g N (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_cnnc)
  have p0004 :=
    @g_id (.classMem N (syn_cnnc))
  have p0005 :=
    @g_snelpw1 N (syn_cnnc)
  have p0006 :=
    @g_sylibr (.classMem N (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) p0004 p0005
  have p0007 :=
    @g_eluni1g (syn_csn N) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))) (syn_cpw1 (syn_cnnc))
  have p0008 :=
    @g_syl (.classMem N (syn_cnnc)) (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) (syn_wb (.classMem (syn_csn N) (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) p0006 p0007
  have p0009 :=
    @g_bitrd (.classMem N (syn_cnnc)) (.classMem N (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))) (.classMem (syn_csn N) (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) p0003 p0008
  have p0010 :=
    @g_eldif (syn_csn (syn_csn N)) (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))
  have p0011 :=
    @g_snelpw1 (syn_csn N) (syn_cpw1 (syn_cnnc))
  have p0012 :=
    @g_snelpw1 N (syn_cnnc)
  have p0013 :=
    @g_bitri (.classMem (syn_csn (syn_csn N)) (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) (.classMem N (syn_cnnc)) p0011 p0012
  have p0014 :=
    @g_anbi1i (.classMem (syn_csn (syn_csn N)) (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) p0013
  have p0015 :=
    @g_bitri (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wa (.classMem (syn_csn (syn_csn N)) (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) (syn_wa (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) p0010 p0014
  have p0016 :=
    @g_a1i (syn_wb (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wa (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))) (.classMem N (syn_cnnc)) p0015
  have p0017 :=
    @g_id (.classMem N (syn_cnnc))
  have p0018 :=
    @g_biantrurd (.classMem N (syn_cnnc)) (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) p0017
  have p0019 :=
    @g_bicomd (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wa (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) p0018
  have p0020 :=
    @g_bitrd (.classMem N (syn_cnnc)) (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wa (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) p0016 p0019
  have p0021 :=
    @g_bitrd (.classMem N (syn_cnnc)) (.classMem N (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))) (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) p0009 p0020
  have p0022 :=
    @g_bitrd (.classMem N (syn_cnnc)) (.classMem N (syn_cwppreachincb F C)) (.classMem N (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) p0002 p0021
  exact p0022

noncomputable def g_wppbrcofnv
    (A : Class) (B : Class) (R : Class) (H : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_wppbrcofnv_1 : Nominal.NPrf (syn_wfn H (syn_cvv))) (hyp_wppbrcofnv_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_ccom R H) B) (syn_wbr (syn_cfv H A) R B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ H.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
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
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cfv H A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wbr (syn_cfv H A) R B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_H, fresh_x_not_B, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brco x A B R H dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_fnbrfvb (syn_cvv) A (.cv x) H
  have p0002 :=
    @g_mp2an (syn_wfn H (syn_cvv)) (.classMem A (syn_cvv)) (syn_wb (.classEq (syn_cfv H A) (.cv x)) (syn_wbr A H (.cv x))) hyp_wppbrcofnv_1 hyp_wppbrcofnv_2 p0001
  have p0003 :=
    @g_bicomi (.classEq (syn_cfv H A) (.cv x)) (syn_wbr A H (.cv x)) p0002
  have p0004 :=
    @g_anbi1i (syn_wbr A H (.cv x)) (.classEq (syn_cfv H A) (.cv x)) (syn_wbr (.cv x) R B) p0003
  have p0005 :=
    @g_eqcom (syn_cfv H A) (.cv x)
  have p0006 :=
    @g_anbi1i (.classEq (syn_cfv H A) (.cv x)) (.classEq (.cv x) (syn_cfv H A)) (syn_wbr (.cv x) R B) p0005
  have p0007 :=
    @g_bitri (syn_wa (syn_wbr A H (.cv x)) (syn_wbr (.cv x) R B)) (syn_wa (.classEq (syn_cfv H A) (.cv x)) (syn_wbr (.cv x) R B)) (syn_wa (.classEq (.cv x) (syn_cfv H A)) (syn_wbr (.cv x) R B)) p0004 p0006
  have p0008 :=
    @g_exbii (syn_wa (syn_wbr A H (.cv x)) (syn_wbr (.cv x) R B)) (syn_wa (.classEq (.cv x) (syn_cfv H A)) (syn_wbr (.cv x) R B)) x p0007
  have p0009 :=
    @g_fvex A H
  have p0010 :=
    @g_breq1 (.cv x) (syn_cfv H A) B R
  have p0011 :=
    @g_ceqsexv (syn_wbr (.cv x) R B) (syn_wbr (syn_cfv H A) R B) x (syn_cfv H A) dv_cache_0005 dv_cache_0006 p0009 p0010
  have p0012 :=
    @g_bitri (syn_wex x (syn_wa (syn_wbr A H (.cv x)) (syn_wbr (.cv x) R B))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_cfv H A)) (syn_wbr (.cv x) R B))) (syn_wbr (syn_cfv H A) R B) p0008 p0011
  have p0013 :=
    @g_bitri (syn_wbr A (syn_ccom R H) B) (syn_wex x (syn_wa (syn_wbr A H (.cv x)) (syn_wbr (.cv x) R B))) (syn_wbr (syn_cfv H A) R B) p0000 p0012
  exact p0013

noncomputable def g_wpppredfamfn
    (C : Class) (F : Class) (hyp_wpppredfamfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwpppredfam F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_eqid (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0001 :=
    @g_cnvex F hyp_wpppredfamfn_1
  have p0002 :=
    @g_imageex (syn_ccnv F) p0001
  have p0003 :=
    @g_frecex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) p0000 p0002
  have p0004 :=
    @g_tcfnex
  have p0005 :=
    @g_coex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn) p0003 p0004
  have p0006 :=
    @g_cnvex (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) p0005
  have p0007 :=
    @g_wppimagefn (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) p0006
  have p0008 :=
    @g_ssetex
  have p0009 :=
    @g_wppimagefn (syn_csset) p0008
  have p0010 :=
    @g_fncovv (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cimage (syn_csset)) p0007 p0009
  have p0011 :=
    (by simpa [syn_cwpppredfam] using (Nominal.classEqRefl (syn_cwpppredfam F C)))
  have p0012 :=
    @g_fneq1i (syn_cvv) (syn_cwpppredfam F C) (syn_ccom (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cimage (syn_csset))) p0011
  have p0013 :=
    @g_mpbir (syn_wfn (syn_cwpppredfam F C) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cimage (syn_csset))) (syn_cvv)) p0010 p0012
  exact p0013

noncomputable def g_wpphitfamfn
    (C : Class) (F : Class) (hyp_wpppredfamfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwpphitfam F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_wpppowlayerseqex C F hyp_wpppredfamfn_1
  have p0001 :=
    @g_cnvex (syn_cwpppowlayerseq F C) p0000
  have p0002 :=
    @g_wppimagefn (syn_ccnv (syn_cwpppowlayerseq F C)) p0001
  have p0003 :=
    @g_ssetex
  have p0004 :=
    @g_wppimagefn (syn_csset) p0003
  have p0005 :=
    @g_fncovv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset)) p0002 p0004
  have p0006 :=
    (by simpa [syn_cwpphitfam] using (Nominal.classEqRefl (syn_cwpphitfam F C)))
  have p0007 :=
    @g_fneq1i (syn_cvv) (syn_cwpphitfam F C) (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset))) p0006
  have p0008 :=
    @g_mpbir (syn_wfn (syn_cwpphitfam F C) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset))) (syn_cvv)) p0005 p0007
  exact p0008

#print axioms g_wpphitfamfn

end NFChoice.DirectNominalPrf.WPPReplay
