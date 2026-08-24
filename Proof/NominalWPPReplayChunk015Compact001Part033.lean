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
import NominalWPPReplayChunk015Compact001Part032

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

noncomputable def g_wppreachincbrng
    (C : Class) (F : Class) (N : Class) (d : Var) (dv_C_d : d ∉ C.fv) (dv_F_d : d ∉ F.fv) (dv_N_d : d ∉ N.fv) (hyp_wppreachincbrng_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wb (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ N.fv ∪ ({d} : Finset Var)
  have dv_cache_0001 : d ∉ ((syn_csn (syn_csn N))).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : d ∉ ((syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppredmemrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphitmemrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((syn_cdm F)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint ((syn_csn (syn_csn (.cv d)))).fv ((syn_ccnv (syn_csset))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint ((syn_csn (syn_csn (.cv d)))).fv ((syn_ccnv (syn_csset))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv]; exact (show Disjoint (((syn_csn (.cv d))).fv) (((syn_csset)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (((Class.cv d)).fv) (((syn_csset)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({d} : Finset Var)) (((syn_csset)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset]; exact (show Disjoint (({d} : Finset Var)) ((∅ : Finset Var)) from (by simp))))))))))
  have p0000 :=
    @g_dfima3 (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))
  have p0001 :=
    @g_eleq2i (syn_cima (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))) (syn_csn (syn_csn N)) p0000
  have p0002 :=
    @g_bicomi (.classMem (syn_csn (syn_csn N)) (syn_cima (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))) (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))) p0001
  have p0003 :=
    @g_elimapw12 d (syn_csn (syn_csn N)) (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cdm F) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_bitri (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))) (.classMem (syn_csn (syn_csn N)) (syn_cima (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))) (syn_wrex d (syn_cdm F) (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)))) p0002 p0003
  have p0005 :=
    @g_elsymdif (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)
  have p0006 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N)))))
  have p0007 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N)))))
  have p0008 :=
    @g_bibi12i (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N))) (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_cwpppredmemrel F C)) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N))) (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_cwpphitmemrel F C)) p0006 p0007
  have p0009 :=
    @g_notbii (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N)))) (syn_wb (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_cwpppredmemrel F C)) (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_cwpphitmemrel F C))) p0008
  have p0010 :=
    @g_bicomi (.neg (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N))))) (.neg (syn_wb (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_cwpppredmemrel F C)) (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_cwpphitmemrel F C)))) p0009
  have p0011 :=
    @g_bitri (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))) (.neg (syn_wb (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_cwpppredmemrel F C)) (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_cwpphitmemrel F C)))) (.neg (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N))))) p0005 p0010
  have p0012 :=
    (by simpa [syn_cwpppredmemrel] using (Nominal.classEqRefl (syn_cwpppredmemrel F C)))
  have p0013 :=
    @g_breqi (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)) (syn_cwpppredmemrel F C) (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpppredfam F C)) p0012
  have p0014 :=
    @g_wpppredfamfn C F hyp_wppreachincbrng_1
  have p0015 :=
    @g_snex (syn_csn (.cv d))
  have p0016 :=
    @g_wppbrcofnv (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)) (syn_ccnv (syn_csset)) (syn_cwpppredfam F C) dv_cache_0004 p0014 p0015
  have p0017 :=
    @g_brcnv (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn N)) (syn_csset)
  have p0018 :=
    @g_snex N
  have p0019 :=
    @g_fvex (syn_csn (syn_csn (.cv d))) (syn_cwpppredfam F C)
  have p0020 :=
    @g_brssetsn (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))) p0018 p0019
  have p0021 :=
    @g_bitri (syn_wbr (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))) (syn_ccnv (syn_csset)) (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn N)) (syn_csset) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) p0017 p0020
  have p0022 :=
    @g_bitri (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpppredfam F C)) (syn_csn (syn_csn N))) (syn_wbr (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))) (syn_ccnv (syn_csset)) (syn_csn (syn_csn N))) (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) p0016 p0021
  have p0023 :=
    @g_bitri (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpppredfam F C)) (syn_csn (syn_csn N))) (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) p0013 p0022
  have p0024 :=
    (by simpa [syn_cwpphitmemrel] using (Nominal.classEqRefl (syn_cwpphitmemrel F C)))
  have p0025 :=
    @g_breqi (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)) (syn_cwpphitmemrel F C) (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpphitfam F C)) p0024
  have p0026 :=
    @g_wpphitfamfn C F hyp_wppreachincbrng_1
  have p0027 :=
    @g_snex (syn_csn (.cv d))
  have p0028 :=
    @g_wppbrcofnv (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)) (syn_ccnv (syn_csset)) (syn_cwpphitfam F C) dv_cache_0004 p0026 p0027
  have p0029 :=
    @g_brcnv (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn N)) (syn_csset)
  have p0030 :=
    @g_snex N
  have p0031 :=
    @g_fvex (syn_csn (syn_csn (.cv d))) (syn_cwpphitfam F C)
  have p0032 :=
    @g_brssetsn (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))) p0030 p0031
  have p0033 :=
    @g_bitri (syn_wbr (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))) (syn_ccnv (syn_csset)) (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn N)) (syn_csset) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))) p0029 p0032
  have p0034 :=
    @g_bitri (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpphitfam F C)) (syn_csn (syn_csn N))) (syn_wbr (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))) (syn_ccnv (syn_csset)) (syn_csn (syn_csn N))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))) p0028 p0033
  have p0035 :=
    @g_bitri (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpphitfam F C)) (syn_csn (syn_csn N))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))) p0025 p0034
  have p0036 :=
    @g_bibi12i (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N))) (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))) p0023 p0035
  have p0037 :=
    @g_notbii (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N)))) (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))) p0036
  have p0038 :=
    @g_bitri (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))) (.neg (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N))))) (.neg (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))) p0011 p0037
  have p0039 :=
    @g_rexbii (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))) (.neg (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))) d (syn_cdm F) p0038
  have p0040 :=
    @g_bitri (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))) (syn_wrex d (syn_cdm F) (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N))) (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)))) (syn_wrex d (syn_cdm F) (.neg (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))) p0004 p0039
  have p0041 :=
    @g_notbii (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F)))))) (syn_wrex d (syn_cdm F) (.neg (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))) p0040
  have p0042 :=
    @g_dfral2 (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))) d (syn_cdm F)
  have p0043 :=
    @g_bicomi (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))) (.neg (syn_wrex d (syn_cdm F) (.neg (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))))) p0042
  have p0044 :=
    @g_bitri (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (.neg (syn_wrex d (syn_cdm F) (.neg (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))))) (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))) p0041 p0043
  exact p0044

noncomputable def g_elwppreachincball
    (C : Class) (F : Class) (N : Class) (d : Var) (dv_C_F : Disjoint C.fv F.fv) (dv_C_N : Disjoint C.fv N.fv) (dv_C_d : d ∉ C.fv) (dv_F_N : Disjoint F.fv N.fv) (dv_F_d : d ∉ F.fv) (dv_N_d : d ∉ N.fv) (hyp_elwppreachincball_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem N (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ N.fv ∪ ({d} : Finset Var)
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : Disjoint (C).fv (N).fv := by
    clear dv_cache_0001
    exact (show Disjoint (C).fv (N).fv from (show Disjoint (C).fv (N).fv from (by exact dv_C_N)))
  have dv_cache_0003 : Disjoint (F).fv (N).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (F).fv (N).fv from (show Disjoint (F).fv (N).fv from (by exact dv_F_N)))
  have dv_cache_0004 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : d ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elwppreachincb C F N dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_wppreachincbrng C F N d dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_elwppreachincball_1
  have p0002 :=
    @g_a1i (syn_wb (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))) (.classMem N (syn_cnnc)) p0001
  have p0003 :=
    @g_bitrd (.classMem N (syn_cnnc)) (.classMem N (syn_cwppreachincb F C)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))) p0000 p0002
  exact p0003

noncomputable def g_wppreachincblayers
    (C : Class) (n : Var) (F : Class) (d : Var) (dv_C_F : Disjoint C.fv F.fv) (dv_C_d : d ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_F_d : d ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_d_n : d ≠ n) (hyp_wppreachincblayers_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))))) := by
  let proofSupport : Finset Var := C.fv ∪ ({n} : Finset Var) ∪ F.fv ∪ ({d} : Finset Var)
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : Disjoint (C).fv ((Class.cv n)).fv := by
    clear dv_cache_0001
    exact (show Disjoint (C).fv ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((C).fv) (({n} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show n ∉ (C).fv from (by exact dv_C_n))))))
  have dv_cache_0003 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (F).fv ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (F).fv ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((F).fv) (({n} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show n ∉ (F).fv from (by exact dv_F_n))))))
  have dv_cache_0005 : d ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : d ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elwppreachincball C F (.cv n) d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_wppreachincblayers_1
  have p0001 :=
    @g_vex d
  have p0002 :=
    @g_elwpppredfam C (.cv d) F n hyp_wppreachincblayers_1 p0001
  have p0003 :=
    @g_vex d
  have p0004 :=
    @g_elwpphitfam C (.cv d) F n hyp_wppreachincblayers_1 p0003
  have p0005 :=
    @g_bibi12i (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) p0002 p0004
  have p0006 :=
    @g_ralbii (syn_wb (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))) d (syn_cdm F) p0005
  have p0007 :=
    @g_a1i (syn_wb (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))))) (.classMem (.cv n) (syn_cnnc)) p0006
  have p0008 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))) p0000 p0007
  exact p0008

noncomputable def g_wpppowcorefn
    (F : Class) (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0001 :=
    @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_wpppostcompex F hyp_wpppowcorefn_1
  have p0004 :=
    @g_elfuns (syn_cwpppostcomp F) p0003
  have p0005 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F)) p0002 p0004
  have p0006 :=
    @g_idex
  have p0007 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0008 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0006 p0009
  have p0011 :=
    @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0012 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0013 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0011 p0014
  have p0016 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F))) (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0005 p0010 p0015
  have p0017 :=
    @g_wpporbitfnndv (syn_cwpppostcomp F) (syn_cid)
  have p0018 :=
    Nominal.mp p0016 p0017
  exact p0018

noncomputable def g_wpppowcore0
    (F : Class) (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0001 :=
    @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_wpppostcompex F hyp_wpppowcorefn_1
  have p0004 :=
    @g_elfuns (syn_cwpppostcomp F) p0003
  have p0005 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F)) p0002 p0004
  have p0006 :=
    @g_idex
  have p0007 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0008 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0006 p0009
  have p0011 :=
    @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0012 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0013 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0011 p0014
  have p0016 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F))) (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0005 p0010 p0015
  have p0017 :=
    @g_wpporbit0ndv (syn_cwpppostcomp F) (syn_cid)
  have p0018 :=
    Nominal.mp p0016 p0017
  exact p0018

noncomputable def g_wpppowcoresuc
    (n : Var) (F : Class) (dv_F_n : n ∉ F.fv) (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))) := by
  let proofSupport : Finset Var := ({n} : Finset Var) ∪ F.fv
  have p0000 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0001 :=
    @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_wpppostcompex F hyp_wpppowcorefn_1
  have p0004 :=
    @g_elfuns (syn_cwpppostcomp F) p0003
  have p0005 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F)) p0002 p0004
  have p0006 :=
    @g_idex
  have p0007 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0008 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0006 p0009
  have p0011 :=
    @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0012 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0013 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0011 p0014
  have p0016 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F))) (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0005 p0010 p0015
  have p0017 :=
    @g_wpporbitsucndv (syn_cwpppostcomp F) (syn_cid) (.cv n)
  have p0018 :=
    @g_mpan (syn_w3a (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F))) (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cwpppostcomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))) p0016 p0017
  have p0019 :=
    @g_fvex (.cv n) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0020 :=
    @g_wpppostcompfv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F hyp_wpppowcorefn_1 p0019
  have p0021 :=
    @g_a1i (.classEq (syn_cfv (syn_cwpppostcomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) p0020
  have p0022 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cwpppostcomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) p0018 p0021
  exact p0022

noncomputable def g_wpppowlayerseqfv
    (C : Class) (n : Var) (F : Class) (dv_C_F : Disjoint C.fv F.fv) (dv_C_n : n ∉ C.fv) (dv_F_n : n ∉ F.fv) (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))))) := by
  let proofSupport : Finset Var := C.fv ∪ ({n} : Finset Var) ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpppowlayerseq] using (Nominal.classEqRefl (syn_cwpppowlayerseq F C)))
  have p0001 :=
    @g_fveq1i (syn_csn (.cv n)) (syn_cwpppowlayerseq F C) (syn_ccom (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cfv (syn_ccom (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n)))) (.classMem (.cv n) (syn_cnnc)) p0001
  have p0003 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0004 :=
    @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_wpppostcompex F hyp_wpppowcorefn_1
  have p0007 :=
    @g_elfuns (syn_cwpppostcomp F) p0006
  have p0008 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F)) p0005 p0007
  have p0009 :=
    @g_idex
  have p0010 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0011 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0009 p0012
  have p0014 :=
    @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0015 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
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
    @g_a1i (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (.classMem (.cv n) (syn_cnnc)) p0029
  have p0031 :=
    @g_nntccl (.cv n)
  have p0032 :=
    @g_vex n
  have p0033 :=
    @g_tcfnfv (.cv n) p0032
  have p0034 :=
    @g_a1i (.classEq (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n))) (.classMem (.cv n) (syn_cnnc)) p0033
  have p0035 :=
    @g_eleq1d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n)) (syn_cnnc) p0034
  have p0036 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0031 p0035
  have p0037 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0038 :=
    @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_wpppostcompex F hyp_wpppowcorefn_1
  have p0041 :=
    @g_elfuns (syn_cwpppostcomp F) p0040
  have p0042 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F)) p0039 p0041
  have p0043 :=
    @g_idex
  have p0044 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0045 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0046 :=
    Nominal.mp p0044 p0045
  have p0047 :=
    @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0043 p0046
  have p0048 :=
    @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0049 :=
    @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0050 :=
    @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0051 :=
    Nominal.mp p0049 p0050
  have p0052 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0048 p0051
  have p0053 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F))) (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0042 p0047 p0052
  have p0054 :=
    @g_wpporbitfnndv (syn_cwpppostcomp F) (syn_cid)
  have p0055 :=
    Nominal.mp p0053 p0054
  have p0056 :=
    @g_fndm (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0057 :=
    Nominal.mp p0055 p0056
  have p0058 :=
    @g_eleq2i (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cnnc) (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) p0057
  have p0059 :=
    @g_a1i (syn_wb (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0058
  have p0060 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)) p0036 p0059
  have p0061 :=
    @g_fntcfn
  have p0062 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0063 :=
    Nominal.mp p0061 p0062
  have p0064 :=
    @g_vex n
  have p0065 :=
    @g_snel1c (.cv n) p0064
  have p0066 :=
    @g_fntcfn
  have p0067 :=
    @g_fndm (syn_c1c) (syn_ctcfn)
  have p0068 :=
    Nominal.mp p0066 p0067
  have p0069 :=
    @g_eleqtrri (syn_csn (.cv n)) (syn_c1c) (syn_cdm (syn_ctcfn)) p0065 p0068
  have p0070 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn))) p0063 p0069
  have p0071 :=
    @g_dmfco (syn_csn (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0072 :=
    Nominal.mp p0070 p0071
  have p0073 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))) (.classMem (.cv n) (syn_cnnc)) p0072
  have p0074 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) p0060 p0073
  have p0075 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) p0030 p0074
  have p0076 :=
    @g_fvco (syn_csn (.cv n)) (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0077 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))) (.classEq (syn_cfv (syn_ccom (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cfv (syn_cwppupperpreop C) (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))))) p0075 p0076
  have p0078 :=
    @g_fntcfn
  have p0079 :=
    @g_vex n
  have p0080 :=
    @g_snel1c (.cv n) p0079
  have p0081 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn (.cv n)) (syn_c1c)) p0078 p0080
  have p0082 :=
    @g_fvco2 (syn_c1c) (syn_csn (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0083 :=
    Nominal.mp p0081 p0082
  have p0084 :=
    @g_vex n
  have p0085 :=
    @g_tcfnfv (.cv n) p0084
  have p0086 :=
    @g_fveq2i (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0085
  have p0087 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) p0083 p0086
  have p0088 :=
    @g_a1i (.classEq (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (.classMem (.cv n) (syn_cnnc)) p0087
  have p0089 :=
    @g_fveq2d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_cwppupperpreop C) p0088
  have p0090 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cfv (syn_cwppupperpreop C) (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n)))) (syn_cfv (syn_cwppupperpreop C) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) p0077 p0089
  have p0091 :=
    @g_fvex (syn_ctc (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0092 :=
    @g_wppupperpreopfv C (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) p0091
  have p0093 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppupperpreop C) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C)))) (.classMem (.cv n) (syn_cnnc)) p0092
  have p0094 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cfv (syn_cwppupperpreop C) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))) p0090 p0093
  have p0095 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cfv (syn_ccom (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))) p0002 p0094
  exact p0095

noncomputable def g_wppimageatex
    (D : Class) (hyp_wppimageatex_1 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppimageat D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv
  have p0000 :=
    (by simpa [syn_cwppimageat] using (Nominal.classEqRefl (syn_cwppimageat D)))
  have p0001 :=
    @g_lnimageopex
  have p0002 :=
    @g_idex
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_snex (syn_csn D)
  have p0005 :=
    @g_xpex (syn_cvv) (syn_csn (syn_csn D)) p0003 p0004
  have p0006 :=
    @g_txpex (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) p0002 p0005
  have p0007 :=
    @g_coex (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) p0001 p0006
  have p0008 :=
    @g_eqeltri (syn_cwppimageat D) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) (syn_cvv) p0000 p0007
  exact p0008

noncomputable def g_wppimageatfn
    (D : Class) (hyp_wppimageatfn_1 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwppimageat D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv
  have p0000 :=
    @g_lnimageopfn
  have p0001 :=
    @g_f1ovi
  have p0002 :=
    @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_snex D
  have p0005 :=
    @g_fnconstg (syn_cvv) (syn_csn D) (syn_cvv)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_inidm (syn_cvv)
  have p0011 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) p0010
  have p0012 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) (syn_cvv)) p0009 p0011
  have p0013 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) p0000 p0012
  have p0014 :=
    (by simpa [syn_cwppimageat] using (Nominal.classEqRefl (syn_cwppimageat D)))
  have p0015 :=
    @g_fneq1i (syn_cvv) (syn_cwppimageat D) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) p0014
  have p0016 :=
    @g_mpbir (syn_wfn (syn_cwppimageat D) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) (syn_cvv)) p0013 p0015
  exact p0016

noncomputable def g_wppimageatfv
    (D : Class) (R : Class) (hyp_wppimageatfv_1 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_wppimageatfv_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppimageat D) R) (syn_cima R (syn_csn D))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cwppimageat] using (Nominal.classEqRefl (syn_cwppimageat D)))
  have p0001 :=
    @g_fveq1i R (syn_cwppimageat D) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) p0000
  have p0002 :=
    @g_f1ovi
  have p0003 :=
    @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_snex D
  have p0006 :=
    @g_fnconstg (syn_cvv) (syn_csn D) (syn_cvv)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) (syn_cvv)) p0004 p0007
  have p0009 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_inidm (syn_cvv)
  have p0012 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) p0011
  have p0013 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) (syn_cvv)) (.classMem R (syn_cvv)) p0013 hyp_wppimageatfv_2
  have p0015 :=
    @g_fvco2 (syn_cvv) R (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_f1ovi
  have p0018 :=
    @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_snex D
  have p0021 :=
    @g_fnconstg (syn_cvv) (syn_csn D) (syn_cvv)
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_fvtxpvv R (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) p0019 p0022 hyp_wppimageatfv_2
  have p0024 :=
    @g_fvi R (syn_cvv)
  have p0025 :=
    Nominal.mp hyp_wppimageatfv_2 p0024
  have p0026 :=
    @g_snex D
  have p0027 :=
    @g_fvconst2 (syn_cvv) (syn_csn D) R p0026
  have p0028 :=
    Nominal.mp hyp_wppimageatfv_2 p0027
  have p0029 :=
    @g_opeq12i (syn_cfv (syn_cid) R) R (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) R) (syn_csn D) p0025 p0028
  have p0030 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) R) (syn_cop (syn_cfv (syn_cid) R) (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) R)) (syn_cop R (syn_csn D)) p0023 p0029
  have p0031 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) R) (syn_cop R (syn_csn D)) (syn_clnimageop) p0030
  have p0032 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) R) (syn_cfv (syn_clnimageop) (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) R)) (syn_cfv (syn_clnimageop) (syn_cop R (syn_csn D))) p0016 p0031
  have p0033 :=
    @g_snex D
  have p0034 :=
    @g_lnimageopval (syn_csn D) R hyp_wppimageatfv_2 p0033
  have p0035 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) R) (syn_cfv (syn_clnimageop) (syn_cop R (syn_csn D))) (syn_cima R (syn_csn D)) p0032 p0034
  have p0036 :=
    @g_eqtri (syn_cfv (syn_cwppimageat D) R) (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) R) (syn_cima R (syn_csn D)) p0001 p0035
  exact p0036

noncomputable def g_wpppowateqex
    (D : Class) (F : Class) (hyp_wpppowateqex_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wpppowateqex_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppowateq F D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpppowateq] using (Nominal.classEqRefl (syn_cwpppowateq F D)))
  have p0001 :=
    @g_wppimageatex D hyp_wpppowateqex_2
  have p0002 :=
    @g_wpppostcompex F hyp_wpppowateqex_1
  have p0003 :=
    @g_eqid (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0004 :=
    @g_frecexg (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cwpppostcomp F) (syn_cid) (syn_cvv) p0003
  have p0005 :=
    Nominal.mp p0002 p0004
  have p0006 :=
    @g_tcfnex
  have p0007 :=
    @g_pm3_2i (.classMem (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cvv)) (.classMem (syn_ctcfn) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_coexg (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn) (syn_cvv) (syn_cvv)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_pm3_2i (.classMem (syn_cwppimageat D) (syn_cvv)) (.classMem (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_cvv)) p0001 p0009
  have p0011 :=
    @g_coexg (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_cvv) (syn_cvv)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_cnvexg (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_cvv)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_eqid (syn_cfrec F D)
  have p0016 :=
    @g_frecexg (syn_cfrec F D) F D (syn_cvv) p0015
  have p0017 :=
    Nominal.mp hyp_wpppowateqex_1 p0016
  have p0018 :=
    @g_siexg (syn_cfrec F D) (syn_cvv)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_pm3_2i (.classMem (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_cvv)) (.classMem (syn_csi (syn_cfrec F D)) (syn_cvv)) p0014 p0019
  have p0021 :=
    @g_coexg (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D)) (syn_cvv) (syn_cvv)
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_fixexg (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D))) (syn_cvv)
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_uni1exg (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D)))) (syn_cvv)
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_eqeltri (syn_cwpppowateq F D) (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D))))) (syn_cvv) p0000 p0026
  exact p0027

#print axioms g_wpppowateqex

end NFChoice.DirectNominalPrf.WPPReplay
