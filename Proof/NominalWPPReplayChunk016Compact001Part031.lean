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
import NominalWPPReplayChunk016Compact001Part030

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

noncomputable def g_wecutisobranchwwknfdv
    (x : Var) (y : Var) (u : Var) (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_u : u ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_E_y : y ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_h : h ∉ S.fv) (dv_S_u : u ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_h_u : h ≠ u) (dv_h_x : h ≠ x) (dv_h_y : h ≠ y) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) (hyp_wecutisobranchknterminalfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisobranchknterminalfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) (hyp_wecutisobranchknterminalfdv_3 : Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf (.imp (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.imp (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({u} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({h} : Finset Var) ∪ E.fv
  have dv_cache_0001 : h ∉ ((syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, dv_h_y, dv_h_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, dv_h_y, dv_h_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))
  have p0001 :=
    Nominal.ax1 (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E))
  have p0002 :=
    @g_a1i (.imp (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0001
  have p0003 :=
    @g_mpd (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))) p0000 p0002
  have p0004 :=
    @g_simpl (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)
  have p0005 :=
    @g_isoeq4 (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) D R S (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0006 :=
    @g_syl (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (syn_wb (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))) p0004 p0005
  have p0007 :=
    @g_biimpd (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0006
  have p0008 :=
    @g_a2i (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0007
  have p0009 :=
    @g_a1i (.imp (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0008
  have p0010 :=
    @g_mpd (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))) p0003 p0009
  have p0011 :=
    @g_simpr (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)
  have p0012 :=
    @g_isoeq5 D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E R S (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0013 :=
    @g_syl (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_wb (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E)) p0011 p0012
  have p0014 :=
    @g_biimpd (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E) p0013
  have p0015 :=
    @g_a2i (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E) p0014
  have p0016 :=
    @g_a1i (.imp (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0015
  have p0017 :=
    @g_mpd (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E)) p0010 p0016
  have p0018 :=
    @g_snex (syn_cop (.cv y) (.cv u))
  have p0019 :=
    @g_unex (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))) hyp_wecutisobranchknterminalfdv_3 p0018
  have p0020 :=
    @g_isoeq1 D E R S (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) (.cv h)
  have p0021 :=
    @g_spcev (syn_wiso (.cv h) R S D E) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E) h (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) dv_cache_0001 dv_cache_0002 p0019 p0020
  have p0022 :=
    @g_a1i (.imp (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E) (syn_wex h (syn_wiso (.cv h) R S D E))) (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) p0021
  have p0023 :=
    @g_a2i (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E) (syn_wex h (syn_wiso (.cv h) R S D E)) p0022
  have p0024 :=
    @g_a1i (.imp (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E)) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) R S D E)))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0023
  have p0025 :=
    @g_mpd (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S D E)) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) R S D E))) p0017 p0024
  have p0026 :=
    @g_n_3mix1 (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0027 :=
    @g_a1i (.imp (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) p0026
  have p0028 :=
    @g_a2i (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0027
  have p0029 :=
    @g_a1i (.imp (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) R S D E))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0028
  have p0030 :=
    @g_mpd (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) R S D E))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0025 p0029
  have p0031 :=
    @g_a1i (.imp (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0030
  exact p0031

#print axioms g_wecutisobranchwwknfdv

end NFChoice.DirectNominalPrf.WPPReplay
