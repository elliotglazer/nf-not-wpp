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
import NominalWPPReplayChunk016Compact001Part055

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

noncomputable def g_wppcardt4fnvalsingndv
    (D : Class) :
    Nominal.NPrf (.imp (.classMem D (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) := by
  let proofSupport : Finset Var := D.fv
  have p0000 :=
    (by simpa [syn_cwppcardt4fn] using (Nominal.classEqRefl (syn_cwppcardt4fn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cwppcardt4fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (.classMem D (syn_cncs)) p0001
  have p0003 :=
    @g_wppcardt2fnmapndv
  have p0004 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt2fn))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_a1i (syn_wf (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem D (syn_cncs)) p0007
  have p0009 :=
    @g_snelpw1 D (syn_cncs)
  have p0010 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0009
  have p0011 :=
    @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0012 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0011
  have p0013 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0010 p0012
  have p0014 :=
    @g_snelpw1 (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0015 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0014
  have p0016 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0013 p0015
  have p0017 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
  have p0018 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0017
  have p0019 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0016 p0018
  have p0020 :=
    @g_jca (.classMem D (syn_cncs)) (syn_wf (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0008 p0019
  have p0021 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))
  have p0022 :=
    @g_syl (.classMem D (syn_cncs)) (syn_wa (syn_wf (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cfv (syn_cwppcardt2fn) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_csn (syn_csn (syn_csn (syn_csn D))))))) p0020 p0021
  have p0023 :=
    @g_snelpw1 D (syn_cncs)
  have p0024 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0023
  have p0025 :=
    @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0026 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0025
  have p0027 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0024 p0026
  have p0028 :=
    @g_snelpw1 (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0029 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0028
  have p0030 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0027 p0029
  have p0031 :=
    @g_wppcardt2fnmapndv
  have p0032 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cncs)) (syn_csn (syn_csn (syn_csn D))) (syn_csi (syn_cwppcardt2fn)) p0033
  have p0035 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_csn (syn_cfv (syn_csi (syn_cwppcardt2fn)) (syn_csn (syn_csn (syn_csn D)))))) p0030 p0034
  have p0036 :=
    @g_snelpw1 D (syn_cncs)
  have p0037 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0036
  have p0038 :=
    @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0039 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0038
  have p0040 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0037 p0039
  have p0041 :=
    @g_wppcardt2fnmapndv
  have p0042 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_csn (syn_csn D)) (syn_cwppcardt2fn) p0041
  have p0043 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classEq (syn_cfv (syn_csi (syn_cwppcardt2fn)) (syn_csn (syn_csn (syn_csn D)))) (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))))) p0040 p0042
  have p0044 :=
    @g_sneqd (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_cwppcardt2fn)) (syn_csn (syn_csn (syn_csn D)))) (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))) p0043
  have p0045 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_csn (syn_cfv (syn_csi (syn_cwppcardt2fn)) (syn_csn (syn_csn (syn_csn D))))) (syn_csn (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))))) p0035 p0044
  have p0046 :=
    @g_wppcardt2fnvalsingndv D
  have p0047 :=
    @g_sneqd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))) (syn_ctc (syn_ctc D)) p0046
  have p0048 :=
    @g_sneqd (.classMem D (syn_cncs)) (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))) (syn_csn (syn_ctc (syn_ctc D))) p0047
  have p0049 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_csn (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))))) (syn_csn (syn_csn (syn_ctc (syn_ctc D)))) p0045 p0048
  have p0050 :=
    @g_fveq2d (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_csn (syn_csn (syn_ctc (syn_ctc D)))) (syn_cwppcardt2fn) p0049
  have p0051 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cfv (syn_cwppcardt2fn) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc D))))) p0022 p0050
  have p0052 :=
    @g_tccl D
  have p0053 :=
    @g_tccl (syn_ctc D)
  have p0054 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc D) (syn_cncs)) (.classMem (syn_ctc (syn_ctc D)) (syn_cncs)) p0052 p0053
  have p0055 :=
    @g_wppcardt2fnvalsingndv (syn_ctc (syn_ctc D))
  have p0056 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc (syn_ctc D)) (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc D))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))) p0054 p0055
  have p0057 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc D))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) p0051 p0056
  have p0058 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) p0002 p0057
  exact p0058

noncomputable def g_cnv2resndv
    (A : Class) (B : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (syn_cin R (syn_cxp A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
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
  have fresh_x_not_R : x ∉ R.fv := by
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
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cin R (syn_cxp A B))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cin R (syn_cxp A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_brcnv (.cv x) (.cv y) (syn_cres (syn_ccnv (syn_cres R A)) B)
  have p0001 :=
    @g_brres (.cv y) (.cv x) (syn_ccnv (syn_cres R A)) B
  have p0002 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y)) (syn_wbr (.cv y) (syn_cres (syn_ccnv (syn_cres R A)) B) (.cv x)) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_cres R A)) (.cv x)) (.classMem (.cv y) B)) p0000 p0001
  have p0003 :=
    @g_brcnv (.cv y) (.cv x) (syn_cres R A)
  have p0004 :=
    @g_anbi1i (syn_wbr (.cv y) (syn_ccnv (syn_cres R A)) (.cv x)) (syn_wbr (.cv x) (syn_cres R A) (.cv y)) (.classMem (.cv y) B) p0003
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y)) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_cres R A)) (.cv x)) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cres R A) (.cv y)) (.classMem (.cv y) B)) p0002 p0004
  have p0006 :=
    @g_brres (.cv x) (.cv y) R A
  have p0007 :=
    @g_anbi1i (syn_wbr (.cv x) (syn_cres R A) (.cv y)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) A)) (.classMem (.cv y) B) p0006
  have p0008 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y)) (syn_wa (syn_wbr (.cv x) (syn_cres R A) (.cv y)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) A)) (.classMem (.cv y) B)) p0005 p0007
  have p0009 :=
    @g_anass (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) A) (.classMem (.cv y) B)
  have p0010 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y)) (syn_wa (syn_wa (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) A)) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) p0008 p0009
  have p0011 :=
    @g_brxp (.cv x) (.cv y) A B
  have p0012 :=
    @g_bicomi (syn_wbr (.cv x) (syn_cxp A B) (.cv y)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0011
  have p0013 :=
    @g_anbi2i (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wbr (.cv x) (syn_cxp A B) (.cv y)) (syn_wbr (.cv x) R (.cv y)) p0012
  have p0014 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_cxp A B) (.cv y))) p0010 p0013
  have p0015 :=
    @g_brin (.cv x) (.cv y) R (syn_cxp A B)
  have p0016 :=
    @g_bicomi (syn_wbr (.cv x) (syn_cin R (syn_cxp A B)) (.cv y)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_cxp A B) (.cv y))) p0015
  have p0017 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_cxp A B) (.cv y))) (syn_wbr (.cv x) (syn_cin R (syn_cxp A B)) (.cv y)) p0014 p0016
  have p0018 :=
    @g_eqbrriv x y (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (syn_cin R (syn_cxp A B)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0017
  exact p0018

noncomputable def g_cnvrngresndv
    (B : Class) (R : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cres (syn_ccnv R) B)) (syn_cin R (syn_cxp (syn_cvv) B))) := by
  let proofSupport : Finset Var := B.fv ∪ R.fv
  have dv_cache_0001 : Disjoint ((syn_cvv)).fv (R).fv := by
    exact (show Disjoint ((syn_cvv)).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show Disjoint ((∅ : Finset Var)) ((R).fv) from (by simp))))
  have p0000 :=
    @g_resid R
  have p0001 :=
    @g_cnveqi (syn_cres R (syn_cvv)) R p0000
  have p0002 :=
    @g_reseq1i (syn_ccnv (syn_cres R (syn_cvv))) (syn_ccnv R) B p0001
  have p0003 :=
    @g_cnveqi (syn_cres (syn_ccnv (syn_cres R (syn_cvv))) B) (syn_cres (syn_ccnv R) B) p0002
  have p0004 :=
    @g_cnv2resndv (syn_cvv) B R dv_cache_0001
  have p0005 :=
    @g_eqtr3i (syn_ccnv (syn_cres (syn_ccnv (syn_cres R (syn_cvv))) B)) (syn_ccnv (syn_cres (syn_ccnv R) B)) (syn_cin R (syn_cxp (syn_cvv) B)) p0003 p0004
  exact p0005

noncomputable def g_hwcodesunivndv
     :
    Nominal.NPrf (.classEq (syn_chwcodes (syn_cvv)) (syn_cwe)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes (syn_cvv))))
  have p0001 :=
    @g_pwv
  have p0002 :=
    @g_xpeq2i (syn_cpw (syn_cvv)) (syn_cvv) (syn_cvv) p0001
  have p0003 :=
    @g_xpvv
  have p0004 :=
    @g_eqtri (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))) (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv) p0002 p0003
  have p0005 :=
    @g_ineq2i (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))) (syn_cvv) (syn_cwe) p0004
  have p0006 :=
    @g_inv1 (syn_cwe)
  have p0007 :=
    @g_eqtri (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw (syn_cvv)))) (syn_cin (syn_cwe) (syn_cvv)) (syn_cwe) p0005 p0006
  have p0008 :=
    @g_eqtri (syn_chwcodes (syn_cvv)) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw (syn_cvv)))) (syn_cwe) p0000 p0007
  exact p0008

noncomputable def g_hwcnunivrrndv
    (A : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) (syn_chwcn A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_cnvrngresndv (syn_cpw A) (syn_chwcn (syn_cvv))
  have p0001 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0002 :=
    @g_ineq1i (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_cpw A)) p0001
  have p0003 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes (syn_cvv))))
  have p0004 :=
    @g_pwv
  have p0005 :=
    @g_xpeq2i (syn_cpw (syn_cvv)) (syn_cvv) (syn_cvv) p0004
  have p0006 :=
    @g_xpvv
  have p0007 :=
    @g_eqtri (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))) (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv) p0005 p0006
  have p0008 :=
    @g_ineq2i (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))) (syn_cvv) (syn_cwe) p0007
  have p0009 :=
    @g_inv1 (syn_cwe)
  have p0010 :=
    @g_eqtri (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw (syn_cvv)))) (syn_cin (syn_cwe) (syn_cvv)) (syn_cwe) p0008 p0009
  have p0011 :=
    @g_eqtri (syn_chwcodes (syn_cvv)) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw (syn_cvv)))) (syn_cwe) p0003 p0010
  have p0012 :=
    @g_ineq1i (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_chwrels) p0011
  have p0013 :=
    @g_ineq1i (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cin (syn_cwe) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_cpw A)) p0012
  have p0014 :=
    @g_eqtri (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cin (syn_cwe) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_cpw A))) p0002 p0013
  have p0015 :=
    @g_in32 (syn_cwe) (syn_chwrels) (syn_cxp (syn_cvv) (syn_cpw A))
  have p0016 :=
    @g_eqtri (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cin (syn_cwe) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_chwrels)) p0014 p0015
  have p0017 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0018 :=
    @g_eqcomi (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) p0017
  have p0019 :=
    @g_ineq1i (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_chwcodes A) (syn_chwrels) p0018
  have p0020 :=
    @g_eqtri (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_chwrels)) (syn_cin (syn_chwcodes A) (syn_chwrels)) p0016 p0019
  have p0021 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0022 :=
    @g_eqcomi (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) p0021
  have p0023 :=
    @g_eqtri (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_chwcn A) p0020 p0022
  have p0024 :=
    @g_eqtri (syn_ccnv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_chwcn A) p0000 p0023
  exact p0024

noncomputable def g_hwnisogendrrndv
    (A : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A))) (syn_chwniso A)) := by
  let proofSupport : Finset Var := A.fv
  have dv_cache_0001 : Disjoint ((syn_chwcn A)).fv ((syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))).fv := by
    exact (show Disjoint ((syn_chwcn A)).fv ((syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima]; exact (show Disjoint ((A).fv) ((((syn_chwgen)).fv) ∪ (((syn_cxp (syn_chwbij) (syn_cvv))).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((syn_chwgen)).fv) from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp)))), (show Disjoint ((A).fv) (((syn_cxp (syn_chwbij) (syn_cvv))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp]; exact (show Disjoint ((A).fv) ((((syn_chwbij)).fv) ∪ (((syn_cvv)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((syn_chwbij)).fv) from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp)))), (show Disjoint ((A).fv) (((syn_cvv)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))⟩))))
  have p0000 :=
    @g_cnv2resndv (syn_chwcn A) (syn_chwcn A) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) dv_cache_0001
  have p0001 :=
    (by simpa [syn_chwniso] using (Nominal.classEqRefl (syn_chwniso A)))
  have p0002 :=
    @g_eqcomi (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0001
  have p0003 :=
    @g_eqtri (syn_ccnv (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A))) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_chwniso A) p0000 p0002
  exact p0003

noncomputable def g_wpppowsetfnexndv
     :
    Nominal.NPrf (.classMem (syn_cwpppowsetfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0001 :=
    @g_ssetex
  have p0002 :=
    @g_cnvex (syn_csset) p0001
  have p0003 :=
    @g_imageex (syn_ccnv (syn_csset)) p0002
  have p0004 :=
    @g_eqeltri (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_wpppowsetfnfnndv
     :
    Nominal.NPrf (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_ssetex
  have p0001 :=
    @g_cnvex (syn_csset) p0000
  have p0002 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0001
  have p0003 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0004 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0003
  have p0005 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0002 p0004
  exact p0005

noncomputable def g_wpppowsetfnvalndv
    (A : Class) (hyp_wpppowsetfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpppowsetfn) (syn_csn A)) (syn_cpw A)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have dv_cache_0001 : x ∉ ((syn_csset)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0000
  have p0002 :=
    @g_ssetex
  have p0003 :=
    @g_cnvex (syn_csset) p0002
  have p0004 :=
    @g_snex A
  have p0005 :=
    @g_fvimagecl (syn_csn A) (syn_ccnv (syn_csset)) p0003 p0004
  have p0006 :=
    @g_iniseg x (syn_csset) A dv_cache_0001 dv_cache_0002
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_brsset (.cv x) A p0007 hyp_wpppowsetfnvalndv_1
  have p0009 :=
    @g_abbii (syn_wbr (.cv x) (syn_csset) A) (syn_wss (.cv x) A) x p0008
  have p0010 :=
    @g_eqtri (syn_cima (syn_ccnv (syn_csset)) (syn_csn A)) (.cab x (syn_wbr (.cv x) (syn_csset) A)) (.cab x (syn_wss (.cv x) A)) p0006 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x A dv_cache_0002
  have p0012 :=
    @g_eqcomi (syn_cpw A) (.cab x (syn_wss (.cv x) A)) p0011
  have p0013 :=
    @g_eqtri (syn_cima (syn_ccnv (syn_csset)) (syn_csn A)) (.cab x (syn_wss (.cv x) A)) (syn_cpw A) p0010 p0012
  have p0014 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_ccnv (syn_csset))) (syn_csn A)) (syn_cima (syn_ccnv (syn_csset)) (syn_csn A)) (syn_cpw A) p0005 p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cwpppowsetfn) (syn_csn A)) (syn_cfv (syn_cimage (syn_ccnv (syn_csset))) (syn_csn A)) (syn_cpw A) p0001 p0014
  exact p0015

noncomputable def g_wpphwcnsetfnvalndv
    (A : Class) (hyp_wpphwcnsetfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)) (syn_chwcn A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0000
  have p0002 :=
    @g_lnimageresfnfn
  have p0003 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0004 :=
    @g_hwcodesunivndv
  have p0005 :=
    @g_weex
  have p0006 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0004 p0005
  have p0007 :=
    @g_hwrelsex
  have p0008 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0006 p0007
  have p0009 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0003 p0008
  have p0010 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0009
  have p0011 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_ssetex
  have p0014 :=
    @g_cnvex (syn_csset) p0013
  have p0015 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0014
  have p0016 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0017 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0016
  have p0018 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0015 p0017
  have p0019 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0012 p0018
  have p0020 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_inidm (syn_cvv)
  have p0023 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0022
  have p0024 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0021 p0023
  have p0025 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0002 p0024
  have p0026 :=
    @g_snex A
  have p0027 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) p0025 p0026
  have p0028 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0031 :=
    @g_hwcodesunivndv
  have p0032 :=
    @g_weex
  have p0033 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0031 p0032
  have p0034 :=
    @g_hwrelsex
  have p0035 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0033 p0034
  have p0036 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0030 p0035
  have p0037 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0036
  have p0038 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_ssetex
  have p0041 :=
    @g_cnvex (syn_csset) p0040
  have p0042 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0041
  have p0043 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0044 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0043
  have p0045 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0042 p0044
  have p0046 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0039 p0045
  have p0047 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_inidm (syn_cvv)
  have p0050 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0049
  have p0051 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0048 p0050
  have p0052 :=
    @g_snex A
  have p0053 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) p0051 p0052
  have p0054 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))
  have p0055 :=
    Nominal.mp p0053 p0054
  have p0056 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0057 :=
    @g_hwcodesunivndv
  have p0058 :=
    @g_weex
  have p0059 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0057 p0058
  have p0060 :=
    @g_hwrelsex
  have p0061 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0059 p0060
  have p0062 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0056 p0061
  have p0063 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0062
  have p0064 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_ssetex
  have p0067 :=
    @g_cnvex (syn_csset) p0066
  have p0068 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0067
  have p0069 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0070 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0069
  have p0071 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0068 p0070
  have p0072 :=
    @g_snex A
  have p0073 :=
    @g_fvtxpvv (syn_csn A) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn) p0065 p0071 p0072
  have p0074 :=
    @g_snex A
  have p0075 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0076 :=
    @g_hwcodesunivndv
  have p0077 :=
    @g_weex
  have p0078 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0076 p0077
  have p0079 :=
    @g_hwrelsex
  have p0080 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0078 p0079
  have p0081 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0075 p0080
  have p0082 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0081
  have p0083 :=
    @g_fvconst2 (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_csn A) p0082
  have p0084 :=
    Nominal.mp p0074 p0083
  have p0085 :=
    @g_wpppowsetfnvalndv A hyp_wpphwcnsetfnvalndv_1
  have p0086 :=
    @g_opeq12i (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_csn A)) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cfv (syn_cwpppowsetfn) (syn_csn A)) (syn_cpw A) p0084 p0085
  have p0087 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_csn A)) (syn_cop (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_csn A)) (syn_cfv (syn_cwpppowsetfn) (syn_csn A))) (syn_cop (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) p0073 p0086
  have p0088 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_csn A)) (syn_cop (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) (syn_clnimageresfn) p0087
  have p0089 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) (syn_csn A)) (syn_cfv (syn_clnimageresfn) (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_csn A))) (syn_cfv (syn_clnimageresfn) (syn_cop (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) p0055 p0088
  have p0090 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0091 :=
    @g_hwcodesunivndv
  have p0092 :=
    @g_weex
  have p0093 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0091 p0092
  have p0094 :=
    @g_hwrelsex
  have p0095 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0093 p0094
  have p0096 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0090 p0095
  have p0097 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0096
  have p0098 :=
    @g_pwex A hyp_wpphwcnsetfnvalndv_1
  have p0099 :=
    @g_lnimageresfnval (syn_cpw A) (syn_ccnv (syn_chwcn (syn_cvv))) p0097 p0098
  have p0100 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) (syn_csn A)) (syn_cfv (syn_clnimageresfn) (syn_cop (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) p0089 p0099
  have p0101 :=
    @g_fveq2i (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) (syn_csn A)) (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) (syn_cimage (syn_cswap)) p0100
  have p0102 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_csn A)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) (syn_csn A))) (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) p0029 p0101
  have p0103 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0104 :=
    @g_hwcodesunivndv
  have p0105 :=
    @g_weex
  have p0106 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0104 p0105
  have p0107 :=
    @g_hwrelsex
  have p0108 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0106 p0107
  have p0109 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0103 p0108
  have p0110 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0109
  have p0111 :=
    @g_pwex A hyp_wpphwcnsetfnvalndv_1
  have p0112 :=
    @g_resex (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A) p0110 p0111
  have p0113 :=
    @g_wppimageswapfv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) p0112
  have p0114 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_csn A)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) (syn_ccnv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) p0102 p0113
  have p0115 :=
    @g_hwcnunivrrndv A
  have p0116 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_csn A)) (syn_ccnv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) (syn_chwcn A) p0114 p0115
  have p0117 :=
    @g_eqtri (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_csn A)) (syn_chwcn A) p0001 p0116
  exact p0117

noncomputable def g_wpphwgendomfnvalndv
    (A : Class) (hyp_wpphwgendomfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpphwgendomfn) (syn_csn A)) (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cwpphwgendomfn] using (Nominal.classEqRefl (syn_cwpphwgendomfn)))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphwgendomfn) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) p0000
  have p0002 :=
    @g_hwgenex
  have p0003 :=
    @g_hwbijex
  have p0004 :=
    @g_vvex
  have p0005 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0003 p0004
  have p0006 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_imageswapfn
  have p0010 :=
    @g_lnimageresfnfn
  have p0011 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0012 :=
    @g_hwcodesunivndv
  have p0013 :=
    @g_weex
  have p0014 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0012 p0013
  have p0015 :=
    @g_hwrelsex
  have p0016 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0014 p0015
  have p0017 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0011 p0016
  have p0018 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0017
  have p0019 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_ssetex
  have p0022 :=
    @g_cnvex (syn_csset) p0021
  have p0023 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0022
  have p0024 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0025 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0024
  have p0026 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0023 p0025
  have p0027 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0020 p0026
  have p0028 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_inidm (syn_cvv)
  have p0031 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0030
  have p0032 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0029 p0031
  have p0033 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0010 p0032
  have p0034 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0009 p0033
  have p0035 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0036 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0035
  have p0037 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0034 p0036
  have p0038 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0008 p0037
  have p0039 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_inidm (syn_cvv)
  have p0042 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0041
  have p0043 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cvv)) p0040 p0042
  have p0044 :=
    @g_snex A
  have p0045 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) p0043 p0044
  have p0046 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_hwgenex
  have p0049 :=
    @g_hwbijex
  have p0050 :=
    @g_vvex
  have p0051 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0049 p0050
  have p0052 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0048 p0051
  have p0053 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)
  have p0054 :=
    Nominal.mp p0052 p0053
  have p0055 :=
    @g_imageswapfn
  have p0056 :=
    @g_lnimageresfnfn
  have p0057 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0058 :=
    @g_hwcodesunivndv
  have p0059 :=
    @g_weex
  have p0060 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0058 p0059
  have p0061 :=
    @g_hwrelsex
  have p0062 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0060 p0061
  have p0063 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0057 p0062
  have p0064 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0063
  have p0065 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0066 :=
    Nominal.mp p0064 p0065
  have p0067 :=
    @g_ssetex
  have p0068 :=
    @g_cnvex (syn_csset) p0067
  have p0069 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0068
  have p0070 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0071 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0070
  have p0072 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0069 p0071
  have p0073 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0066 p0072
  have p0074 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_inidm (syn_cvv)
  have p0077 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0076
  have p0078 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0075 p0077
  have p0079 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0056 p0078
  have p0080 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0055 p0079
  have p0081 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0082 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0081
  have p0083 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0080 p0082
  have p0084 :=
    @g_snex A
  have p0085 :=
    @g_fvtxpvv (syn_csn A) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn) p0054 p0083 p0084
  have p0086 :=
    @g_snex A
  have p0087 :=
    @g_hwgenex
  have p0088 :=
    @g_hwbijex
  have p0089 :=
    @g_vvex
  have p0090 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0088 p0089
  have p0091 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0087 p0090
  have p0092 :=
    @g_fvconst2 (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_csn A) p0091
  have p0093 :=
    Nominal.mp p0086 p0092
  have p0094 :=
    @g_wpphwcnsetfnvalndv A hyp_wpphwgendomfnvalndv_1
  have p0095 :=
    @g_opeq12i (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_csn A)) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)) (syn_chwcn A) p0093 p0094
  have p0096 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_csn A)) (syn_cop (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_csn A)) (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A))) (syn_cop (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)) p0085 p0095
  have p0097 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_csn A)) (syn_cop (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)) (syn_clnimageresfn) p0096
  have p0098 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_csn A)) (syn_cfv (syn_clnimageresfn) (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_csn A))) (syn_cfv (syn_clnimageresfn) (syn_cop (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) p0047 p0097
  have p0099 :=
    @g_hwgenex
  have p0100 :=
    @g_hwbijex
  have p0101 :=
    @g_vvex
  have p0102 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0100 p0101
  have p0103 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0099 p0102
  have p0104 :=
    @g_hwcnex A hyp_wpphwgendomfnvalndv_1
  have p0105 :=
    @g_lnimageresfnval (syn_chwcn A) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) p0103 p0104
  have p0106 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_csn A)) (syn_cfv (syn_clnimageresfn) (syn_cop (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)) p0098 p0105
  have p0107 :=
    @g_eqtri (syn_cfv (syn_cwpphwgendomfn) (syn_csn A)) (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_csn A)) (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)) p0001 p0106
  exact p0107

#print axioms g_wpphwgendomfnvalndv

end NFChoice.DirectNominalPrf.WPPReplay
