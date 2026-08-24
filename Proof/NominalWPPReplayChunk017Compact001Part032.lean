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
import NominalWPPReplayChunk017Compact001Part031

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

noncomputable def g_hnwcutcodestrictextendndv
    (x : Var) (z : Var) (w : Var) (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_u_z : u ≠ z) (dv_v_z : v ≠ z) (dv_w_z : w ≠ z) (dv_x_z : x ≠ z) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({z} : Finset Var) ∪ ({w} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : v ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, (Ne.symm dv_u_z), (Ne.symm dv_v_z), (Ne.symm dv_w_z), (Ne.symm dv_x_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0001 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0002 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0003 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0004 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0003
  have p0005 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem A (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_hwnisoer A
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A)) p0005 p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0009 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0010 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0009
  have p0011 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0010
  have p0012 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0011
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv u) (syn_chwcn A)) p0008 p0012
  have p0014 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0015 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0016 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0015
  have p0017 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0016
  have p0018 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0017
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv v) (syn_chwcn A)) p0014 p0018
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0021 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0022 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0020 p0022
  have p0024 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0019 p0023
  have p0025 :=
    @g_hnwcutcodeambientndv x v A dv_cache_0001
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwcn A)) p0024 p0025
  have p0027 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0028 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0029 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0028
  have p0030 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0029
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv w) (syn_chwcn A)) p0027 p0030
  have p0032 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0033 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))) p0032
  have p0034 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) p0031 p0033
  have p0035 :=
    @g_hnwcutcodeambientndv z w A dv_cache_0002
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wa (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)) (syn_chwcn A)) p0034 p0035
  have p0037 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0038 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0039 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0038
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0037 p0039
  have p0041 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0042 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))) p0041
  have p0043 :=
    @g_ertrd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_chwcn A) (syn_chwniso A) (.cv u) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)) p0007 p0013 p0026 p0036 p0040 p0042
  have p0044 :=
    @g_exp32 (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv w))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))) p0043
  have p0045 :=
    @g_reximdvai (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))) z (syn_cfv (syn_c2nd) (.cv w)) dv_cache_0003 p0044
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.imp (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) p0001 p0045
  have p0047 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))) p0000 p0046
  exact p0047

noncomputable def g_hncodecmptransisonisondv
    (w : Var) (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))) := by
  let proofSupport : Finset Var := ({w} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_w : z ≠ w := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0001 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0000
  have p0002 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0001
  have p0003 :=
    @g_hwnisoer A
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A)) p0002 p0003
  have p0005 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0006 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0005
  have p0007 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0006
  have p0008 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0007
  have p0009 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0008
  have p0010 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0011 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0010
  have p0012 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0011
  have p0013 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0012
  have p0014 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0013
  have p0015 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0016 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0015
  have p0017 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0016
  have p0018 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0017
  have p0019 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0020 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0019
  have p0021 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0022 :=
    @g_ertrd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_chwcn A) (syn_chwniso A) (.cv u) (.cv v) (.cv w) p0004 p0009 p0014 p0018 p0020 p0021
  have p0023 :=
    @g_orc (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) p0022 p0023
  have p0025 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0026 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0025
  have p0027 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0026
  have p0028 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0027
  have p0029 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0028
  have p0030 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0031 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0030
  have p0032 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0031
  have p0033 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0032
  have p0034 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0029 p0033
  have p0035 :=
    @g_hncodecmpsetstrictcutsemclndv z A (.cv u) (.cv w) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z)))))) p0034 p0035
  have p0037 :=
    @g_biimprd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) p0036
  have p0038 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w))) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) (syn_wrex z (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv z))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0024 p0037
  exact p0038

#print axioms g_hncodecmptransisonisondv

end NFChoice.DirectNominalPrf.WPPReplay
