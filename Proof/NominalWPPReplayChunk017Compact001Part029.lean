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
import NominalWPPReplayChunk017Compact001Part028

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

noncomputable def g_hnwcutcodeisoimagendv
    (x : Var) (v : Var) (u : Var) (A : Class) (h : Var) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({h} : Finset Var)
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_ne_x : g ≠ x := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_g : x ≠ g :=
    Ne.symm fresh_g_ne_x
  have fresh_g_ne_v : g ≠ v := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_ne_g : v ≠ g :=
    Ne.symm fresh_g_ne_v
  have fresh_g_ne_u : g ≠ u := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_g : u ≠ g :=
    Ne.symm fresh_g_ne_u
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_ne_h : g ≠ h := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_g : h ≠ g :=
    Ne.symm fresh_g_ne_h
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ ((syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_h, fresh_g_ne_u, fresh_g_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_x, fresh_g_ne_u, fresh_g_ne_h, fresh_g_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : g ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : g ∉ ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_x, fresh_g_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : g ∉ ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_x, fresh_g_ne_h, fresh_g_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0001 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0000
  have p0002 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0003 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0002
  have p0004 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0001 p0003
  have p0005 :=
    @g_isostrictsegresndv x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv h)
  have p0006 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) p0004 p0005
  have p0007 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0008 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0007
  have p0009 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0010 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0009
  have p0011 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0008 p0010
  have p0012 :=
    @g_hnwcutcodepartsndv x u A dv_cache_0001
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0011 p0012
  have p0014 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) p0013
  have p0015 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0014
  have p0016 :=
    @g_isoeq2 (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wb (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) p0015 p0016
  have p0018 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0019 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0018
  have p0020 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0021 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0020
  have p0022 :=
    @g_isof1o (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0021 p0022
  have p0024 :=
    @g_f1of (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv h)
  have p0025 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0023 p0024
  have p0026 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0027 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0026
  have p0028 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0025 p0027
  have p0029 :=
    @g_ffvelrn (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x) (.cv h)
  have p0030 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) p0028 p0029
  have p0031 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) p0019 p0030
  have p0032 :=
    @g_hnwcutcodepartsclndv v A (syn_cfv (.cv h) (.cv x)) dv_cache_0002
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) p0031 p0032
  have p0034 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) p0033
  have p0035 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) p0034
  have p0036 :=
    @g_isoeq3 (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))
  have p0037 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))) (syn_wb (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) p0035 p0036
  have p0038 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) p0017 p0037
  have p0039 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0040 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0039
  have p0041 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0042 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0041
  have p0043 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0040 p0042
  have p0044 :=
    @g_hnwcutcodepartsndv x u A dv_cache_0001
  have p0045 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0043 p0044
  have p0046 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) p0045
  have p0047 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) p0046
  have p0048 :=
    @g_isoeq4 (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))
  have p0049 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wb (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) p0047 p0048
  have p0050 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) p0038 p0049
  have p0051 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0052 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0051
  have p0053 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0054 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0053
  have p0055 :=
    @g_isof1o (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0056 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0054 p0055
  have p0057 :=
    @g_f1of (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv h)
  have p0058 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0056 p0057
  have p0059 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0060 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0059
  have p0061 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0058 p0060
  have p0062 :=
    @g_ffvelrn (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x) (.cv h)
  have p0063 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) p0061 p0062
  have p0064 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) p0052 p0063
  have p0065 :=
    @g_hnwcutcodepartsclndv v A (syn_cfv (.cv h) (.cv x)) dv_cache_0002
  have p0066 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) p0064 p0065
  have p0067 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) p0066
  have p0068 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) p0067
  have p0069 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))
  have p0070 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))) (syn_wb (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))))) p0068 p0069
  have p0071 :=
    @g_bitrd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))) p0050 p0070
  have p0072 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x))))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (syn_cfv (.cv h) (.cv x)))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))) p0006 p0071
  have p0073 :=
    @g_vex h
  have p0074 :=
    @g_a1i (.classMem (.cv h) (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) p0073
  have p0075 :=
    @g_fvex (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_c2nd)
  have p0076 :=
    @g_a1i (.classMem (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) p0075
  have p0077 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0078 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0077
  have p0079 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0080 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0079
  have p0081 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0078 p0080
  have p0082 :=
    @g_hnwcutcodepartsndv x u A dv_cache_0001
  have p0083 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))))) p0081 p0082
  have p0084 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) p0083
  have p0085 :=
    @g_eleq1d (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cvv) p0084
  have p0086 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cvv)) (.classMem (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0076 p0085
  have p0087 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv h) (syn_cvv)) (.classMem (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0074 p0086
  have p0088 :=
    @g_resexg (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cvv) (syn_cvv)
  have p0089 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv h) (syn_cvv)) (.classMem (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x)))) (syn_cvv))) (.classMem (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) p0087 p0088
  have p0090 :=
    @g_isoeq1 (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (.cv g)
  have p0091 :=
    @g_spcegv (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))) g (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cvv) dv_cache_0003 dv_cache_0004 p0090
  have p0092 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) (.imp (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))))) p0089 p0091
  have p0093 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (syn_cres (.cv h) (syn_cin (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))))) p0072 p0092
  have p0094 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0095 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0094
  have p0096 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0097 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0096
  have p0098 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0095 p0097
  have p0099 :=
    @g_hnwcutcodeambientndv x u A dv_cache_0001
  have p0100 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0098 p0099
  have p0101 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0102 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0101
  have p0103 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0104 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0103
  have p0105 :=
    @g_isof1o (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0106 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0104 p0105
  have p0107 :=
    @g_f1of (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv h)
  have p0108 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf1o (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0106 p0107
  have p0109 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
  have p0110 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0109
  have p0111 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0108 p0110
  have p0112 :=
    @g_ffvelrn (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x) (.cv h)
  have p0113 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (syn_wf (.cv h) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) p0111 p0112
  have p0114 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v))) p0102 p0113
  have p0115 :=
    @g_hnwcutcodeambientclndv v A (syn_cfv (.cv h) (.cv x)) dv_cache_0002
  have p0116 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cfv (.cv h) (.cv x)) (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))) (syn_chwcn A)) p0114 p0115
  have p0117 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))) (syn_chwcn A)) p0100 p0116
  have p0118 :=
    @g_hwnisodirectisobclndv A (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))) g dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0119 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))) (syn_chwcn A))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x))))))) p0117 p0118
  have p0120 :=
    @g_biimprd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))))) p0119
  have p0121 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (.cv h) (.cv x)))) p0093 p0120
  exact p0121

#print axioms g_hnwcutcodeisoimagendv

end NFChoice.DirectNominalPrf.WPPReplay
