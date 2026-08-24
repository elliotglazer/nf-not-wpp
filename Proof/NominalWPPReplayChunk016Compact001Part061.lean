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
import NominalWPPReplayChunk016Compact001Part060

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

noncomputable def g_wppcardt6fnvalsingndv
    (D : Class) :
    Nominal.NPrf (.imp (.classMem D (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) := by
  let proofSupport : Finset Var := D.fv
  have p0000 :=
    (by simpa [syn_cwppcardt6fn] using (Nominal.classEqRefl (syn_cwppcardt6fn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_cwppcardt6fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))) (.classMem D (syn_cncs)) p0001
  have p0003 :=
    @g_wppcardt4fnmapndv
  have p0004 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_a1i (syn_wf (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem D (syn_cncs)) p0007
  have p0009 :=
    @g_id (.classMem D (syn_cncs))
  have p0010 :=
    @g_snelpw1 D (syn_cncs)
  have p0011 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0010
  have p0012 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0009 p0011
  have p0013 :=
    @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0014 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0013
  have p0015 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0012 p0014
  have p0016 :=
    @g_snelpw1 (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0017 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0016
  have p0018 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0015 p0017
  have p0019 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
  have p0020 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0019
  have p0021 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0018 p0020
  have p0022 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
  have p0023 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0022
  have p0024 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0021 p0023
  have p0025 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
  have p0026 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0025
  have p0027 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) p0024 p0026
  have p0028 :=
    @g_jca (.classMem D (syn_cncs)) (syn_wf (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) p0008 p0027
  have p0029 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0030 :=
    @g_syl (.classMem D (syn_cncs)) (syn_wa (syn_wf (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))) (.classEq (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_cfv (syn_cwppcardt2fn) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))))) p0028 p0029
  have p0031 :=
    @g_id (.classMem D (syn_cncs))
  have p0032 :=
    @g_snelpw1 D (syn_cncs)
  have p0033 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0032
  have p0034 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0031 p0033
  have p0035 :=
    @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0036 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0035
  have p0037 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0034 p0036
  have p0038 :=
    @g_snelpw1 (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0039 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0038
  have p0040 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0037 p0039
  have p0041 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
  have p0042 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0041
  have p0043 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0040 p0042
  have p0044 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
  have p0045 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0044
  have p0046 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0043 p0045
  have p0047 :=
    @g_wppcardt4fnmapndv
  have p0048 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn)
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cncs)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_csi (syn_cwppcardt4fn)) p0049
  have p0051 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classEq (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_csn (syn_cfv (syn_csi (syn_cwppcardt4fn)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))) p0046 p0050
  have p0052 :=
    @g_id (.classMem D (syn_cncs))
  have p0053 :=
    @g_snelpw1 D (syn_cncs)
  have p0054 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0053
  have p0055 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0052 p0054
  have p0056 :=
    @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0057 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0056
  have p0058 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0055 p0057
  have p0059 :=
    @g_snelpw1 (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0060 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0059
  have p0061 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0058 p0060
  have p0062 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
  have p0063 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0062
  have p0064 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0061 p0063
  have p0065 :=
    @g_wppcardt4fnmapndv
  have p0066 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cwppcardt4fn) p0065
  have p0067 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classEq (syn_cfv (syn_csi (syn_cwppcardt4fn)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D))))))) p0064 p0066
  have p0068 :=
    @g_sneqd (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_cwppcardt4fn)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D)))))) p0067
  have p0069 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_csn (syn_cfv (syn_csi (syn_cwppcardt4fn)) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_csn (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D))))))) p0051 p0068
  have p0070 :=
    @g_wppcardt4fnvalsingndv D
  have p0071 :=
    @g_sneqd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) p0070
  have p0072 :=
    @g_sneqd (.classMem D (syn_cncs)) (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D)))))) (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))) p0071
  have p0073 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_csn (syn_csn (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) p0069 p0072
  have p0074 :=
    @g_fveq2d (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cwppcardt2fn) p0073
  have p0075 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_cfv (syn_cwppcardt2fn) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D)))))))) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) p0030 p0074
  have p0076 :=
    @g_tccl D
  have p0077 :=
    @g_tccl (syn_ctc D)
  have p0078 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc D) (syn_cncs)) (.classMem (syn_ctc (syn_ctc D)) (syn_cncs)) p0076 p0077
  have p0079 :=
    @g_tccl (syn_ctc (syn_ctc D))
  have p0080 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc (syn_ctc D)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc D))) (syn_cncs)) p0078 p0079
  have p0081 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc D)))
  have p0082 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc D))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) (syn_cncs)) p0080 p0081
  have p0083 :=
    @g_wppcardt2fnvalsingndv (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))
  have p0084 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) p0082 p0083
  have p0085 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) p0075 p0084
  have p0086 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn D))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) p0002 p0085
  exact p0086

noncomputable def g_wppconcrete6fnfnndv
     :
    Nominal.NPrf (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_enex
  have p0001 :=
    @g_wppimagefn (syn_cen) p0000
  have p0002 :=
    @g_wpplitphnordpointfnexndv
  have p0003 :=
    @g_wppimagefn (syn_cwpplitphnordpointfn) p0002
  have p0004 :=
    @g_wppfamilyrep2fnfnndv
  have p0005 :=
    @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0006 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_wppdirecth1famfnfnndv
  have p0011 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0012 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwppdirecth1famfn))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0020 :=
    @g_mpbi (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_cvv)) (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0009 p0020
  have p0022 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    (by simpa [syn_cwppdirecth2famfn] using (Nominal.classEqRefl (syn_cwppdirecth2famfn)))
  have p0025 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn) (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) p0024
  have p0026 :=
    @g_mpbir (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0023 p0025
  have p0027 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn)
  have p0028 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wf (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0026 p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cen)) (syn_cvv)) (syn_wf (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0001 p0028
  have p0030 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    (by simpa [syn_cwppconcrete6codefn] using (Nominal.classEqRefl (syn_cwppconcrete6codefn)))
  have p0033 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppconcrete6codefn) (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) p0032
  have p0034 :=
    @g_mpbir (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0031 p0033
  have p0035 :=
    @g_wppcardt2fnf1ndv
  have p0036 :=
    @g_wppcardt4fnf1ndv
  have p0037 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn) p0036
  have p0038 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0037
  have p0039 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0035 p0038
  have p0040 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    (by simpa [syn_cwppcardt6fn] using (Nominal.classEqRefl (syn_cwppcardt6fn)))
  have p0043 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_mpbir (syn_wf1 (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) p0041 p0044
  have p0046 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn)
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_f1ofn (syn_crn (syn_cwppcardt6fn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_ccnv (syn_cwppcardt6fn))
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_wppcardt2fnf1ndv
  have p0051 :=
    @g_wppcardt4fnf1ndv
  have p0052 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn) p0051
  have p0053 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0052
  have p0054 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0050 p0053
  have p0055 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    (by simpa [syn_cwppcardt6fn] using (Nominal.classEqRefl (syn_cwppcardt6fn)))
  have p0058 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0059 :=
    Nominal.mp p0057 p0058
  have p0060 :=
    @g_mpbir (syn_wf1 (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) p0056 p0059
  have p0061 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn)
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_f1of (syn_crn (syn_cwppcardt6fn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_ccnv (syn_cwppcardt6fn))
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_frn (syn_crn (syn_cwppcardt6fn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_ccnv (syn_cwppcardt6fn))
  have p0066 :=
    Nominal.mp p0064 p0065
  have p0067 :=
    @g_ssv (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0068 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cvv)
  have p0069 :=
    Nominal.mp p0067 p0068
  have p0070 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cvv))
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0073 :=
    Nominal.mp p0071 p0072
  have p0074 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_pm3_2i (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0066 p0075
  have p0077 :=
    @g_sstr (syn_crn (syn_ccnv (syn_cwppcardt6fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0078 :=
    Nominal.mp p0076 p0077
  have p0079 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccnv (syn_cwppcardt6fn)) (syn_crn (syn_cwppcardt6fn))) (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0034 p0049 p0078
  have p0080 :=
    @g_fnco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))
  have p0081 :=
    Nominal.mp p0079 p0080
  have p0082 :=
    (by simpa [syn_cwppconcrete6fn] using (Nominal.classEqRefl (syn_cwppconcrete6fn)))
  have p0083 :=
    @g_fneq1i (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn) (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) p0082
  have p0084 :=
    @g_mpbir (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn))) (syn_wfn (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) (syn_crn (syn_cwppcardt6fn))) p0081 p0083
  exact p0084

noncomputable def g_wppconcrete6fndmndv
     :
    Nominal.NPrf (.classEq (syn_cdm (syn_cwppconcrete6fn)) (syn_crn (syn_cwppcardt6fn))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_enex
  have p0001 :=
    @g_wppimagefn (syn_cen) p0000
  have p0002 :=
    @g_wpplitphnordpointfnexndv
  have p0003 :=
    @g_wppimagefn (syn_cwpplitphnordpointfn) p0002
  have p0004 :=
    @g_wppfamilyrep2fnfnndv
  have p0005 :=
    @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0006 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_wppdirecth1famfnfnndv
  have p0011 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0012 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwppdirecth1famfn))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0020 :=
    @g_mpbi (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_cvv)) (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0009 p0020
  have p0022 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    (by simpa [syn_cwppdirecth2famfn] using (Nominal.classEqRefl (syn_cwppdirecth2famfn)))
  have p0025 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn) (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) p0024
  have p0026 :=
    @g_mpbir (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0023 p0025
  have p0027 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn)
  have p0028 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wf (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0026 p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cen)) (syn_cvv)) (syn_wf (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0001 p0028
  have p0030 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    (by simpa [syn_cwppconcrete6codefn] using (Nominal.classEqRefl (syn_cwppconcrete6codefn)))
  have p0033 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppconcrete6codefn) (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) p0032
  have p0034 :=
    @g_mpbir (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0031 p0033
  have p0035 :=
    @g_wppcardt2fnf1ndv
  have p0036 :=
    @g_wppcardt4fnf1ndv
  have p0037 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn) p0036
  have p0038 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0037
  have p0039 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0035 p0038
  have p0040 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    (by simpa [syn_cwppcardt6fn] using (Nominal.classEqRefl (syn_cwppcardt6fn)))
  have p0043 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_mpbir (syn_wf1 (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) p0041 p0044
  have p0046 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn)
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_f1ofn (syn_crn (syn_cwppcardt6fn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_ccnv (syn_cwppcardt6fn))
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_wppcardt2fnf1ndv
  have p0051 :=
    @g_wppcardt4fnf1ndv
  have p0052 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn) p0051
  have p0053 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0052
  have p0054 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0050 p0053
  have p0055 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    (by simpa [syn_cwppcardt6fn] using (Nominal.classEqRefl (syn_cwppcardt6fn)))
  have p0058 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0059 :=
    Nominal.mp p0057 p0058
  have p0060 :=
    @g_mpbir (syn_wf1 (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) p0056 p0059
  have p0061 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn)
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_f1of (syn_crn (syn_cwppcardt6fn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_ccnv (syn_cwppcardt6fn))
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_frn (syn_crn (syn_cwppcardt6fn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_ccnv (syn_cwppcardt6fn))
  have p0066 :=
    Nominal.mp p0064 p0065
  have p0067 :=
    @g_ssv (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0068 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cvv)
  have p0069 :=
    Nominal.mp p0067 p0068
  have p0070 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cvv))
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0073 :=
    Nominal.mp p0071 p0072
  have p0074 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_pm3_2i (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0066 p0075
  have p0077 :=
    @g_sstr (syn_crn (syn_ccnv (syn_cwppcardt6fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0078 :=
    Nominal.mp p0076 p0077
  have p0079 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccnv (syn_cwppcardt6fn)) (syn_crn (syn_cwppcardt6fn))) (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0034 p0049 p0078
  have p0080 :=
    @g_fnco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))
  have p0081 :=
    Nominal.mp p0079 p0080
  have p0082 :=
    (by simpa [syn_cwppconcrete6fn] using (Nominal.classEqRefl (syn_cwppconcrete6fn)))
  have p0083 :=
    @g_fneq1i (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn) (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) p0082
  have p0084 :=
    @g_mpbir (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn))) (syn_wfn (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) (syn_crn (syn_cwppcardt6fn))) p0081 p0083
  have p0085 :=
    @g_fndm (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn)
  have p0086 :=
    Nominal.mp p0084 p0085
  exact p0086

noncomputable def g_wppconcrete6fnfunsndv
     :
    Nominal.NPrf (.classMem (syn_cwppconcrete6fn) (syn_cfuns)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_enex
  have p0001 :=
    @g_wppimagefn (syn_cen) p0000
  have p0002 :=
    @g_wpplitphnordpointfnexndv
  have p0003 :=
    @g_wppimagefn (syn_cwpplitphnordpointfn) p0002
  have p0004 :=
    @g_wppfamilyrep2fnfnndv
  have p0005 :=
    @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0006 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv)) (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_wppdirecth1famfnfnndv
  have p0011 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0012 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwppdirecth1famfn))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0020 :=
    @g_mpbi (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_cvv)) (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0009 p0020
  have p0022 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    (by simpa [syn_cwppdirecth2famfn] using (Nominal.classEqRefl (syn_cwppdirecth2famfn)))
  have p0025 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn) (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) p0024
  have p0026 :=
    @g_mpbir (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0023 p0025
  have p0027 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppdirecth2famfn)
  have p0028 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wf (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0026 p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cen)) (syn_cvv)) (syn_wf (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv)) p0001 p0028
  have p0030 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    (by simpa [syn_cwppconcrete6codefn] using (Nominal.classEqRefl (syn_cwppconcrete6codefn)))
  have p0033 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cwppconcrete6codefn) (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) p0032
  have p0034 :=
    @g_mpbir (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0031 p0033
  have p0035 :=
    @g_wppcardt2fnf1ndv
  have p0036 :=
    @g_wppcardt4fnf1ndv
  have p0037 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn) p0036
  have p0038 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0037
  have p0039 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0035 p0038
  have p0040 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    (by simpa [syn_cwppcardt6fn] using (Nominal.classEqRefl (syn_cwppcardt6fn)))
  have p0043 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_mpbir (syn_wf1 (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) p0041 p0044
  have p0046 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn)
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_f1ofn (syn_crn (syn_cwppcardt6fn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_ccnv (syn_cwppcardt6fn))
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_wppcardt2fnf1ndv
  have p0051 :=
    @g_wppcardt4fnf1ndv
  have p0052 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn) p0051
  have p0053 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn)) p0052
  have p0054 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt4fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0050 p0053
  have p0055 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    (by simpa [syn_cwppcardt6fn] using (Nominal.classEqRefl (syn_cwppcardt6fn)))
  have p0058 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
  have p0059 :=
    Nominal.mp p0057 p0058
  have p0060 :=
    @g_mpbir (syn_wf1 (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs)) p0056 p0059
  have p0061 :=
    @g_f1cnv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn)
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_f1of (syn_crn (syn_cwppcardt6fn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_ccnv (syn_cwppcardt6fn))
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_frn (syn_crn (syn_cwppcardt6fn)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_ccnv (syn_cwppcardt6fn))
  have p0066 :=
    Nominal.mp p0064 p0065
  have p0067 :=
    @g_ssv (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0068 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cvv)
  have p0069 :=
    Nominal.mp p0067 p0068
  have p0070 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cvv))
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0073 :=
    Nominal.mp p0071 p0072
  have p0074 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_pm3_2i (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0066 p0075
  have p0077 :=
    @g_sstr (syn_crn (syn_ccnv (syn_cwppcardt6fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0078 :=
    Nominal.mp p0076 p0077
  have p0079 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwppconcrete6codefn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wfn (syn_ccnv (syn_cwppcardt6fn)) (syn_crn (syn_cwppcardt6fn))) (syn_wss (syn_crn (syn_ccnv (syn_cwppcardt6fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0034 p0049 p0078
  have p0080 :=
    @g_fnco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))
  have p0081 :=
    Nominal.mp p0079 p0080
  have p0082 :=
    (by simpa [syn_cwppconcrete6fn] using (Nominal.classEqRefl (syn_cwppconcrete6fn)))
  have p0083 :=
    @g_fneq1i (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn) (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) p0082
  have p0084 :=
    @g_mpbir (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn))) (syn_wfn (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) (syn_crn (syn_cwppcardt6fn))) p0081 p0083
  have p0085 :=
    @g_fnfun (syn_crn (syn_cwppcardt6fn)) (syn_cwppconcrete6fn)
  have p0086 :=
    Nominal.mp p0084 p0085
  have p0087 :=
    (by simpa [syn_cwppconcrete6fn] using (Nominal.classEqRefl (syn_cwppconcrete6fn)))
  have p0088 :=
    (by simpa [syn_cwppconcrete6codefn] using (Nominal.classEqRefl (syn_cwppconcrete6codefn)))
  have p0089 :=
    @g_enex
  have p0090 :=
    @g_imageex (syn_cen) p0089
  have p0091 :=
    (by simpa [syn_cwppdirecth2famfn] using (Nominal.classEqRefl (syn_cwppdirecth2famfn)))
  have p0092 :=
    @g_wpplitphnordpointfnexndv
  have p0093 :=
    @g_imageex (syn_cwpplitphnordpointfn) p0092
  have p0094 :=
    @g_wppfamilyrep2fnexndv
  have p0095 :=
    @g_coex (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn) p0093 p0094
  have p0096 :=
    @g_wppdirecth1famfnexndv
  have p0097 :=
    @g_siex (syn_cwppdirecth1famfn) p0096
  have p0098 :=
    @g_siex (syn_csi (syn_cwppdirecth1famfn)) p0097
  have p0099 :=
    @g_coex (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn))) p0095 p0098
  have p0100 :=
    @g_eqeltri (syn_cwppdirecth2famfn) (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_cvv) p0091 p0099
  have p0101 :=
    @g_coex (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn) p0090 p0100
  have p0102 :=
    @g_eqeltri (syn_cwppconcrete6codefn) (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)) (syn_cvv) p0088 p0101
  have p0103 :=
    (by simpa [syn_cwppcardt6fn] using (Nominal.classEqRefl (syn_cwppcardt6fn)))
  have p0104 :=
    @g_wppcardt2fnexndv
  have p0105 :=
    @g_wppcardt4fnexndv
  have p0106 :=
    @g_siex (syn_cwppcardt4fn) p0105
  have p0107 :=
    @g_siex (syn_csi (syn_cwppcardt4fn)) p0106
  have p0108 :=
    @g_coex (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))) p0104 p0107
  have p0109 :=
    @g_eqeltri (syn_cwppcardt6fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) (syn_cvv) p0103 p0108
  have p0110 :=
    @g_cnvex (syn_cwppcardt6fn) p0109
  have p0111 :=
    @g_coex (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn)) p0102 p0110
  have p0112 :=
    @g_eqeltri (syn_cwppconcrete6fn) (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn))) (syn_cvv) p0087 p0111
  have p0113 :=
    @g_elfuns (syn_cwppconcrete6fn) p0112
  have p0114 :=
    @g_mpbir (.classMem (syn_cwppconcrete6fn) (syn_cfuns)) (syn_wfun (syn_cwppconcrete6fn)) p0086 p0113
  exact p0114

#print axioms g_wppconcrete6fnfunsndv

end NFChoice.DirectNominalPrf.WPPReplay
