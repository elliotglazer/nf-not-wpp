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
import NominalWPPReplayChunk014Compact001Part044

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

noncomputable def g_elstrictseg
    (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0001 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv y)
  have p0002 :=
    @g_brdif (.cv y) (.cv x) R (syn_cid)
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_ideq (.cv y) (.cv x) p0003
  have p0005 :=
    @g_notbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x)) p0004
  have p0006 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv y) (.cv x))))
  have p0007 :=
    @g_bitr4i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (.neg (.classEq (.cv y) (.cv x))) (syn_wne (.cv y) (.cv x)) p0005 p0006
  have p0008 :=
    @g_anbi2i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_wne (.cv y) (.cv x)) (syn_wbr (.cv y) R (.cv x)) p0007
  have p0009 :=
    @g_bitri (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (.neg (syn_wbr (.cv y) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0002 p0008
  have p0010 :=
    @g_bitri (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0001 p0009
  have p0011 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) (.classMem (.cv y) D) p0010
  have p0012 :=
    @g_bitri (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0000 p0011
  exact p0012

noncomputable def g_strictsegdown
    (x : Var) (y : Var) (z : Var) (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_simp2 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0001 :=
    @g_simprd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D) p0000
  have p0002 :=
    @g_simp1 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0003 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0002
  have p0004 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0005 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0004
  have p0006 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0007 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0005 p0006
  have p0008 :=
    @g_biimpi (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0007
  have p0009 :=
    @g_syl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0003 p0008
  have p0010 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0009
  have p0011 :=
    @g_sopc D R
  have p0012 :=
    @g_sylib (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cstrict) D) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0010 p0011
  have p0013 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0012
  have p0014 :=
    @g_porta D R
  have p0015 :=
    @g_sylib (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cpartial) D) (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D)) p0013 p0014
  have p0016 :=
    @g_simp2d (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0015
  have p0017 :=
    @g_simp2 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0018 :=
    @g_simprd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D) p0017
  have p0019 :=
    @g_simp2 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0020 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D) p0019
  have p0021 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0022 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv y)
  have p0023 :=
    @g_brdif (.cv y) (.cv x) R (syn_cid)
  have p0024 :=
    @g_vex x
  have p0025 :=
    @g_ideq (.cv y) (.cv x) p0024
  have p0026 :=
    @g_notbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x)) p0025
  have p0027 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv y) (.cv x))))
  have p0028 :=
    @g_bitr4i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (.neg (.classEq (.cv y) (.cv x))) (syn_wne (.cv y) (.cv x)) p0026 p0027
  have p0029 :=
    @g_anbi2i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_wne (.cv y) (.cv x)) (syn_wbr (.cv y) R (.cv x)) p0028
  have p0030 :=
    @g_bitri (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (.neg (syn_wbr (.cv y) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0023 p0029
  have p0031 :=
    @g_bitri (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0022 p0030
  have p0032 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) (.classMem (.cv y) D) p0031
  have p0033 :=
    @g_bitri (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0021 p0032
  have p0034 :=
    @g_biimpi (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0033
  have p0035 :=
    @g_syl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0020 p0034
  have p0036 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0035
  have p0037 :=
    @g_simp1 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0038 :=
    @g_simprd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0037
  have p0039 :=
    @g_simp3 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0040 :=
    @g_simp2 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0041 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D) p0040
  have p0042 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0043 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv y)
  have p0044 :=
    @g_brdif (.cv y) (.cv x) R (syn_cid)
  have p0045 :=
    @g_vex x
  have p0046 :=
    @g_ideq (.cv y) (.cv x) p0045
  have p0047 :=
    @g_notbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x)) p0046
  have p0048 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv y) (.cv x))))
  have p0049 :=
    @g_bitr4i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (.neg (.classEq (.cv y) (.cv x))) (syn_wne (.cv y) (.cv x)) p0047 p0048
  have p0050 :=
    @g_anbi2i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_wne (.cv y) (.cv x)) (syn_wbr (.cv y) R (.cv x)) p0049
  have p0051 :=
    @g_bitri (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (.neg (syn_wbr (.cv y) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0044 p0050
  have p0052 :=
    @g_bitri (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0043 p0051
  have p0053 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) (.classMem (.cv y) D) p0052
  have p0054 :=
    @g_bitri (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0042 p0053
  have p0055 :=
    @g_biimpi (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0054
  have p0056 :=
    @g_syl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0041 p0055
  have p0057 :=
    @g_simprd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0056
  have p0058 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0057
  have p0059 :=
    @g_trd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) D R (.cv z) (.cv y) (.cv x) p0016 p0018 p0036 p0038 p0039 p0058
  have p0060 :=
    @g_simp2 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0061 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D) p0060
  have p0062 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0063 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv y)
  have p0064 :=
    @g_brdif (.cv y) (.cv x) R (syn_cid)
  have p0065 :=
    @g_vex x
  have p0066 :=
    @g_ideq (.cv y) (.cv x) p0065
  have p0067 :=
    @g_notbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x)) p0066
  have p0068 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv y) (.cv x))))
  have p0069 :=
    @g_bitr4i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (.neg (.classEq (.cv y) (.cv x))) (syn_wne (.cv y) (.cv x)) p0067 p0068
  have p0070 :=
    @g_anbi2i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_wne (.cv y) (.cv x)) (syn_wbr (.cv y) R (.cv x)) p0069
  have p0071 :=
    @g_bitri (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (.neg (syn_wbr (.cv y) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0064 p0070
  have p0072 :=
    @g_bitri (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0063 p0071
  have p0073 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) (.classMem (.cv y) D) p0072
  have p0074 :=
    @g_bitri (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0062 p0073
  have p0075 :=
    @g_biimpi (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0074
  have p0076 :=
    @g_syl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0061 p0075
  have p0077 :=
    @g_simprd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0076
  have p0078 :=
    @g_simprd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0077
  have p0079 :=
    @g_simpl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))
  have p0080 :=
    @g_simp1 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0081 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0080
  have p0082 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0083 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0082
  have p0084 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0085 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0083 p0084
  have p0086 :=
    @g_biimpi (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0085
  have p0087 :=
    @g_syl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0081 p0086
  have p0088 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0087
  have p0089 :=
    @g_sopc D R
  have p0090 :=
    @g_sylib (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cstrict) D) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0088 p0089
  have p0091 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0090
  have p0092 :=
    @g_porta D R
  have p0093 :=
    @g_sylib (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cpartial) D) (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D)) p0091 p0092
  have p0094 :=
    @g_simp3d (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0093
  have p0095 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cantisym) D) p0079 p0094
  have p0096 :=
    @g_simpl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))
  have p0097 :=
    @g_simp1 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0098 :=
    @g_simprd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0097
  have p0099 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv x) D) p0096 p0098
  have p0100 :=
    @g_simpl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))
  have p0101 :=
    @g_simp2 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0102 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D) p0101
  have p0103 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0104 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv y)
  have p0105 :=
    @g_brdif (.cv y) (.cv x) R (syn_cid)
  have p0106 :=
    @g_vex x
  have p0107 :=
    @g_ideq (.cv y) (.cv x) p0106
  have p0108 :=
    @g_notbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x)) p0107
  have p0109 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv y) (.cv x))))
  have p0110 :=
    @g_bitr4i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (.neg (.classEq (.cv y) (.cv x))) (syn_wne (.cv y) (.cv x)) p0108 p0109
  have p0111 :=
    @g_anbi2i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_wne (.cv y) (.cv x)) (syn_wbr (.cv y) R (.cv x)) p0110
  have p0112 :=
    @g_bitri (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (.neg (syn_wbr (.cv y) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0105 p0111
  have p0113 :=
    @g_bitri (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0104 p0112
  have p0114 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) (.classMem (.cv y) D) p0113
  have p0115 :=
    @g_bitri (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0103 p0114
  have p0116 :=
    @g_biimpi (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0115
  have p0117 :=
    @g_syl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0102 p0116
  have p0118 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0117
  have p0119 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) D) p0100 p0118
  have p0120 :=
    @g_simpr (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))
  have p0121 :=
    @g_simpl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))
  have p0122 :=
    @g_simp3 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0123 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr (.cv z) R (.cv y)) p0121 p0122
  have p0124 :=
    @g_eqbrtrrd (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) (.cv z) (.cv x) (.cv y) R p0120 p0123
  have p0125 :=
    @g_simpl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))
  have p0126 :=
    @g_simp2 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))
  have p0127 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D) p0126
  have p0128 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0129 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv y)
  have p0130 :=
    @g_brdif (.cv y) (.cv x) R (syn_cid)
  have p0131 :=
    @g_vex x
  have p0132 :=
    @g_ideq (.cv y) (.cv x) p0131
  have p0133 :=
    @g_notbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x)) p0132
  have p0134 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv y) (.cv x))))
  have p0135 :=
    @g_bitr4i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (.neg (.classEq (.cv y) (.cv x))) (syn_wne (.cv y) (.cv x)) p0133 p0134
  have p0136 :=
    @g_anbi2i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_wne (.cv y) (.cv x)) (syn_wbr (.cv y) R (.cv x)) p0135
  have p0137 :=
    @g_bitri (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (.neg (syn_wbr (.cv y) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0130 p0136
  have p0138 :=
    @g_bitri (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0129 p0137
  have p0139 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) (.classMem (.cv y) D) p0138
  have p0140 :=
    @g_bitri (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0128 p0139
  have p0141 :=
    @g_biimpi (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0140
  have p0142 :=
    @g_syl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0127 p0141
  have p0143 :=
    @g_simprd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0142
  have p0144 :=
    @g_simpld (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0143
  have p0145 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr (.cv y) R (.cv x)) p0125 p0144
  have p0146 :=
    @g_antid (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) D R (.cv x) (.cv y) p0095 p0099 p0119 p0124 p0145
  have p0147 :=
    @g_eqcomd (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) (.cv x) (.cv y) p0146
  have p0148 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv y) (.cv x))))
  have p0149 :=
    @g_biimpi (syn_wne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x))) p0148
  have p0150 :=
    @g_a1i (.imp (syn_wne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x)))) (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) p0149
  have p0151 :=
    @g_mt2d (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x))) (syn_wne (.cv y) (.cv x)) (.classEq (.cv y) (.cv x)) p0147 p0150
  have p0152 :=
    @g_ex (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)) (.neg (syn_wne (.cv y) (.cv x))) p0151
  have p0153 :=
    @g_necon2ad (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wne (.cv y) (.cv x)) (.cv z) (.cv x) p0152
  have p0154 :=
    @g_mpd (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wne (.cv y) (.cv x)) (syn_wne (.cv z) (.cv x)) p0078 p0153
  have p0155 :=
    @g_jca (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0059 p0154
  have p0156 :=
    @g_jca (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))) p0001 p0155
  have p0157 :=
    @g_elstrictseg x z D R
  have p0158 :=
    @g_biimpri (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))) p0157
  have p0159 :=
    @g_syl (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (syn_wa (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0156 p0158
  exact p0159

#print axioms g_strictsegdown

end NFChoice.DirectNominalPrf.WPPReplay
