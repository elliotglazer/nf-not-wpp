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
import NominalWPPReplayChunk017Compact001Part026

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

noncomputable def g_hnwcutcodepartsndv
    (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0001 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0000 p0001
  have p0003 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c1st) p0002
  have p0004 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0005 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0006 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0004 p0005
  have p0007 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c2nd) p0006
  have p0008 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u))) (.classEq (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u))) p0003 p0007
  have p0009 :=
    @g_hnwcutcodeeq12ndv x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u))) (.classEq (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) p0008 p0009
  have p0011 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_c1st) p0010
  have p0012 :=
    @g_eqcomd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) p0011
  have p0013 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0014 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0015 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0014 p0015
  have p0017 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c2nd) p0016
  have p0018 :=
    @g_eleq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u)) (.cv x) p0017
  have p0019 :=
    @g_mpbird (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0013 p0018
  have p0020 :=
    @g_hncodetotalleftmemndv u A dv_cache_0001
  have p0021 :=
    @g_hwcnweclndv A (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_wecutisogencodeparts x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) p0022
  have p0024 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) p0019 p0023
  have p0025 :=
    @g_simpld (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))) p0024
  have p0026 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0027 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0028 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0026 p0027
  have p0029 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c1st) p0028
  have p0030 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0031 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0032 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0030 p0031
  have p0033 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c2nd) p0032
  have p0034 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0035 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0036 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0034 p0035
  have p0037 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c1st) p0036
  have p0038 :=
    @g_difeq1d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u)) (syn_cid) p0037
  have p0039 :=
    @g_cnveqd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid)) (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)) p0038
  have p0040 :=
    @g_imaeq1d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)) p0039
  have p0041 :=
    @g_ineq12d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))) p0033 p0040
  have p0042 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0043 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0044 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0042 p0043
  have p0045 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c2nd) p0044
  have p0046 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0047 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0048 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0046 p0047
  have p0049 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c1st) p0048
  have p0050 :=
    @g_difeq1d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u)) (syn_cid) p0049
  have p0051 :=
    @g_cnveqd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid)) (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)) p0050
  have p0052 :=
    @g_imaeq1d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)) p0051
  have p0053 :=
    @g_ineq12d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))) p0045 p0052
  have p0054 :=
    @g_xpeq12d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) p0041 p0053
  have p0055 :=
    @g_ineq12d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) p0029 p0054
  have p0056 :=
    @g_n_3eqtrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0012 p0025 p0055
  have p0057 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0058 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0059 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0057 p0058
  have p0060 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c1st) p0059
  have p0061 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0062 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0063 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0061 p0062
  have p0064 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c2nd) p0063
  have p0065 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u))) (.classEq (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u))) p0060 p0064
  have p0066 :=
    @g_hnwcutcodeeq12ndv x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
  have p0067 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u))) (.classEq (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) p0065 p0066
  have p0068 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_c2nd) p0067
  have p0069 :=
    @g_eqcomd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) p0068
  have p0070 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0071 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0072 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0073 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0071 p0072
  have p0074 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c2nd) p0073
  have p0075 :=
    @g_eleq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u)) (.cv x) p0074
  have p0076 :=
    @g_mpbird (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0070 p0075
  have p0077 :=
    @g_hncodetotalleftmemndv u A dv_cache_0001
  have p0078 :=
    @g_hwcnweclndv A (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0079 :=
    Nominal.mp p0077 p0078
  have p0080 :=
    @g_wecutisogencodeparts x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) p0079
  have p0081 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) p0076 p0080
  have p0082 :=
    @g_simprd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))) p0081
  have p0083 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0084 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0085 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0083 p0084
  have p0086 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c2nd) p0085
  have p0087 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0088 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0089 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0087 p0088
  have p0090 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c1st) p0089
  have p0091 :=
    @g_difeq1d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u)) (syn_cid) p0090
  have p0092 :=
    @g_cnveqd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid)) (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)) p0091
  have p0093 :=
    @g_imaeq1d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)) p0092
  have p0094 :=
    @g_ineq12d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))) p0086 p0093
  have p0095 :=
    @g_n_3eqtrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) p0069 p0082 p0094
  have p0096 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) p0056 p0095
  exact p0096

noncomputable def g_hnwcutcodeambientclndv
    (u : Var) (A : Class) (B : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem B (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chwcn A))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint (({x} : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({x} : Finset Var)) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) (({u} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ u from (by exact fresh_x_ne_u)))))))), (show Disjoint (({x} : Finset Var)) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint (({x} : Finset Var)) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chwcn A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutcodeeq3 (.cv x) B (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001
  have p0001 :=
    @g_eleq1 (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chwcn A)
  have p0002 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)) (syn_wb (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chwcn A))) p0000 p0001
  have p0003 :=
    @g_imbi2d (.classEq (.cv x) B) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0002
  have p0004 :=
    @g_hnwcutcodeambientndv x u A dv_cache_0002
  have p0005 :=
    @g_expcom (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0004
  have p0006 :=
    @g_vtoclga (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A))) (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chwcn A))) x B (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0003 p0005
  have p0007 :=
    @g_impcom (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chwcn A)) p0006
  exact p0007

#print axioms g_hnwcutcodeambientclndv

end NFChoice.DirectNominalPrf.WPPReplay
