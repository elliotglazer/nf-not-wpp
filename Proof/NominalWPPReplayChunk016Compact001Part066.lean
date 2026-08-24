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
import NominalWPPReplayChunk016Compact001Part065

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

noncomputable def g_hnsicodemapexgndv
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chnsicodemap A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chnsicodemap] using (Nominal.classEqRefl (syn_chnsicodemap A)))
  have p0001 :=
    @g_a1i (.classEq (syn_chnsicodemap A) (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A)))) (.classMem A (syn_cvv)) p0000
  have p0002 :=
    @g_hnsicodeliftfnexndv
  have p0003 :=
    @g_a1i (.classMem (syn_chnsicodeliftfn) (syn_cvv)) (.classMem A (syn_cvv)) p0002
  have p0004 :=
    @g_hwcnexg A
  have p0005 :=
    @g_pw1exg (syn_chwcn A) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chnsicodeliftfn) (syn_cvv)) (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_resexg (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A)) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chnsicodeliftfn) (syn_cvv)) (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv))) (.classMem (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_eqeltrd (.classMem A (syn_cvv)) (syn_chnsicodemap A) (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv) p0001 p0009
  exact p0010

noncomputable def g_hnsicodemapvalndv
    (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))) := by
  let proofSupport : Finset Var := A.fv ∪ ({q} : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_ne_q : u ≠ q := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_u : q ≠ u :=
    Ne.symm fresh_u_ne_q
  have dv_cache_0001 : u ∉ ((syn_cuni (.cv q))).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Wff.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((Wff.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chnsicodemap] using (Nominal.classEqRefl (syn_chnsicodemap A)))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_chnsicodemap A) (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (.cv q))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0001
  have p0003 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_chwcn A)) (syn_chnsicodeliftfn)
  have p0004 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (.cv q)) (syn_cfv (syn_chnsicodeliftfn) (.cv q)) p0002 p0003
  have p0005 :=
    @g_hnwpw1argcl (syn_chwcn A) q
  have p0006 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005
  have p0007 :=
    @g_hnwpw1argcl (syn_chwcn A) q
  have p0008 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0007
  have p0009 :=
    @g_elex (syn_cuni (.cv q)) (syn_chwcn A)
  have p0010 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0011 :=
    @g_eleq1d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_chwcn A) p0010
  have p0012 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0013 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0014 :=
    @g_fveq2d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_c1st) p0013
  have p0015 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0016 :=
    @g_fveq2d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_c2nd) p0015
  have p0017 :=
    @g_opeq12d (.classEq (.cv u) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0014 p0016
  have p0018 :=
    @g_eqeq12d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0012 p0017
  have p0019 :=
    @g_imbi12d (.classEq (.cv u) (syn_cuni (.cv q))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0011 p0018
  have p0020 :=
    @g_hwcnpair u A
  have p0021 :=
    @g_vtoclg (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) u (syn_cuni (.cv q)) (syn_cvv) dv_cache_0001 dv_cache_0002 p0019 p0020
  have p0022 :=
    @g_mpcom (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0009 p0021
  have p0023 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0008 p0022
  have p0024 :=
    @g_sneqd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0023
  have p0025 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0006 p0024
  have p0026 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_chnsicodeliftfn) p0025
  have p0027 :=
    @g_hnwpw1argcl (syn_chwcn A) q
  have p0028 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0027
  have p0029 :=
    @g_elex (syn_cuni (.cv q)) (syn_chwcn A)
  have p0030 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0031 :=
    @g_eleq1d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_chwcn A) p0030
  have p0032 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0033 :=
    @g_fveq2d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_c1st) p0032
  have p0034 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0035 :=
    @g_fveq2d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_c2nd) p0034
  have p0036 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0037 :=
    @g_fveq2d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_c2nd) p0036
  have p0038 :=
    @g_xpeq12d (.classEq (.cv u) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0035 p0037
  have p0039 :=
    @g_sseq12d (.classEq (.cv u) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0033 p0038
  have p0040 :=
    @g_imbi12d (.classEq (.cv u) (syn_cuni (.cv q))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0031 p0039
  have p0041 :=
    @g_hwcnsupp u A
  have p0042 :=
    @g_vtoclg (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) u (syn_cuni (.cv q)) (syn_cvv) dv_cache_0001 dv_cache_0003 p0040 p0041
  have p0043 :=
    @g_mpcom (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0029 p0042
  have p0044 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0028 p0043
  have p0045 :=
    @g_ssv (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
  have p0046 :=
    @g_ssv (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
  have p0047 :=
    @g_pm3_2i (syn_wss (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cvv)) (syn_wss (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cvv)) p0045 p0046
  have p0048 :=
    @g_xpss12 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cvv) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cvv)
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_a1i (syn_wss (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0049
  have p0051 :=
    @g_sstrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cxp (syn_cvv) (syn_cvv)) p0044 p0050
  have p0052 :=
    @g_fvex (syn_cuni (.cv q)) (syn_c1st)
  have p0053 :=
    @g_fvex (syn_cuni (.cv q)) (syn_c2nd)
  have p0054 :=
    @g_hnsicodeliftfnvalgndv (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) p0052 p0053
  have p0055 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cxp (syn_cvv) (syn_cvv))) (.classEq (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) p0051 p0054
  have p0056 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_cfv (syn_chnsicodeliftfn) (.cv q)) (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0026 p0055
  have p0057 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodeliftfn) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) p0004 p0056
  exact p0057

noncomputable def g_hnsicodemapfndv
    (A : Class) :
    Nominal.NPrf (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_q_ne_u : q ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_cuni (.cv q))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((Wff.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q)))) (syn_chwcn (syn_cpw1 A))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodeliftfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_chwcn (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_chnsicodemap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnsicodeliftfnfnndv
  have p0001 :=
    @g_ssv (syn_cpw1 (syn_chwcn A))
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_chnsicodeliftfn) (syn_cvv)) (syn_wss (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_fnssres (syn_cvv) (syn_cpw1 (syn_chwcn A)) (syn_chnsicodeliftfn)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    (by simpa [syn_chnsicodemap] using (Nominal.classEqRefl (syn_chnsicodemap A)))
  have p0006 :=
    @g_fneq1i (syn_cpw1 (syn_chwcn A)) (syn_chnsicodemap A) (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A))) (syn_wfn (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (syn_cpw1 (syn_chwcn A))) p0004 p0006
  have p0008 :=
    @g_hnsicodeliftfnfnndv
  have p0009 :=
    @g_ssv (syn_cpw1 (syn_chwcn A))
  have p0010 :=
    @g_pm3_2i (syn_wfn (syn_chnsicodeliftfn) (syn_cvv)) (syn_wss (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_fnssres (syn_cvv) (syn_cpw1 (syn_chwcn A)) (syn_chnsicodeliftfn)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    (by simpa [syn_chnsicodemap] using (Nominal.classEqRefl (syn_chnsicodemap A)))
  have p0014 :=
    @g_fneq1i (syn_cpw1 (syn_chwcn A)) (syn_chnsicodemap A) (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) p0013
  have p0015 :=
    @g_mpbir (syn_wfn (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A))) (syn_wfn (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (syn_cpw1 (syn_chwcn A))) p0012 p0014
  have p0016 :=
    (by simpa [syn_chnsicodemap] using (Nominal.classEqRefl (syn_chnsicodemap A)))
  have p0017 :=
    @g_fveq1i (.cv q) (syn_chnsicodemap A) (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) p0016
  have p0018 :=
    @g_a1i (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (.cv q))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0017
  have p0019 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_chwcn A)) (syn_chnsicodeliftfn)
  have p0020 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (.cv q)) (syn_cfv (syn_chnsicodeliftfn) (.cv q)) p0018 p0019
  have p0021 :=
    @g_hnwpw1argcl (syn_chwcn A) q
  have p0022 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0021
  have p0023 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnsicodeliftfn) p0022
  have p0024 :=
    @g_hnwpw1argcl (syn_chwcn A) q
  have p0025 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0024
  have p0026 :=
    @g_elex (syn_cuni (.cv q)) (syn_chwcn A)
  have p0027 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0028 :=
    @g_eleq1d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_chwcn A) p0027
  have p0029 :=
    @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0030 :=
    @g_sneqd (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) p0029
  have p0031 :=
    @g_fveq2d (.classEq (.cv u) (syn_cuni (.cv q))) (syn_csn (.cv u)) (syn_csn (syn_cuni (.cv q))) (syn_chnsicodeliftfn) p0030
  have p0032 :=
    @g_eleq1d (.classEq (.cv u) (syn_cuni (.cv q))) (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u))) (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q)))) (syn_chwcn (syn_cpw1 A)) p0031
  have p0033 :=
    @g_imbi12d (.classEq (.cv u) (syn_cuni (.cv q))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q)))) (syn_chwcn (syn_cpw1 A))) p0028 p0032
  have p0034 :=
    @g_hwcnpair u A
  have p0035 :=
    @g_sneqd (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0034
  have p0036 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn A)) (syn_csn (.cv u)) (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnsicodeliftfn) p0035
  have p0037 :=
    @g_hwcnsupp u A
  have p0038 :=
    @g_ssv (syn_cfv (syn_c2nd) (.cv u))
  have p0039 :=
    @g_ssv (syn_cfv (syn_c2nd) (.cv u))
  have p0040 :=
    @g_pm3_2i (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)) p0038 p0039
  have p0041 :=
    @g_xpss12 (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv) (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)
  have p0042 :=
    Nominal.mp p0040 p0041
  have p0043 :=
    @g_a1i (syn_wss (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv u) (syn_chwcn A)) p0042
  have p0044 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cxp (syn_cvv) (syn_cvv)) p0037 p0043
  have p0045 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0046 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0047 :=
    @g_hnsicodeliftfnvalgndv (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) p0045 p0046
  have p0048 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cvv) (syn_cvv))) (.classEq (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0044 p0047
  have p0049 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u))) (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0036 p0048
  have p0050 :=
    @g_hnsicodeliftcodeclndv u A dv_cache_0001
  have p0051 :=
    @g_eqeltrd (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn (syn_cpw1 A)) p0049 p0050
  have p0052 :=
    @g_vtoclg (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A)))) (.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q)))) (syn_chwcn (syn_cpw1 A)))) u (syn_cuni (.cv q)) (syn_cvv) dv_cache_0002 dv_cache_0003 p0033 p0051
  have p0053 :=
    @g_mpcom (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q)))) (syn_chwcn (syn_cpw1 A))) p0026 p0052
  have p0054 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q)))) (syn_chwcn (syn_cpw1 A))) p0025 p0053
  have p0055 :=
    @g_eqeltrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_cfv (syn_chnsicodeliftfn) (.cv q)) (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q)))) (syn_chwcn (syn_cpw1 A)) p0023 p0054
  have p0056 :=
    @g_eqeltrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodeliftfn) (.cv q)) (syn_chwcn (syn_cpw1 A)) p0020 p0055
  have p0057 :=
    @g_rgen (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A))) q (syn_cpw1 (syn_chwcn A)) p0056
  have p0058 :=
    @g_pm3_2i (syn_wfn (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A))) (syn_wral q (syn_cpw1 (syn_chwcn A)) (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A)))) p0015 p0057
  have p0059 :=
    @g_fnfvrnss q (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_chnsicodemap A) dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0060 :=
    Nominal.mp p0058 p0059
  have p0061 :=
    @g_pm3_2i (syn_wfn (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A))) (syn_wss (syn_crn (syn_chnsicodemap A)) (syn_chwcn (syn_cpw1 A))) p0007 p0060
  have p0062 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))))
  have p0063 :=
    @g_mpbir (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (syn_wfn (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A))) (syn_wss (syn_crn (syn_chnsicodemap A)) (syn_chwcn (syn_cpw1 A)))) p0061 p0062
  exact p0063

noncomputable def g_pw1typedbrndv
    (D : Class) (R : Class) (q : Var) (p : Var) (dv_D_p : p ∉ D.fv) (dv_D_q : q ∉ D.fv) (dv_R_p : p ∉ R.fv) (dv_R_q : q ∉ R.fv) (dv_p_q : p ≠ q) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q)) (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q))))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({q} : Finset Var) ∪ ({p} : Finset Var)
  have p0000 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0001 :=
    @g_hnwpw1argcl D p
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (.classMem (.cv p) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0002 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0006 :=
    @g_hnwpw1argcl D q
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0005 p0006
  have p0008 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0007 p0008
  have p0010 :=
    @g_breq12d (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (.cv p) (syn_csn (syn_cuni (.cv p))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_csi R) p0004 p0009
  have p0011 :=
    @g_vex p
  have p0012 :=
    @g_uniex (.cv p) p0011
  have p0013 :=
    @g_vex q
  have p0014 :=
    @g_uniex (.cv q) p0013
  have p0015 :=
    @g_brsnsi (syn_cuni (.cv p)) (syn_cuni (.cv q)) R p0012 p0014
  have p0016 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi R) (syn_csn (syn_cuni (.cv q)))) (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) p0015
  have p0017 :=
    @g_bitrd (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) (syn_wbr (.cv p) (syn_csi R) (.cv q)) (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi R) (syn_csn (syn_cuni (.cv q)))) (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q))) p0010 p0016
  exact p0017

noncomputable def g_pw1argclcl
    (D : Class) (Q : Class) :
    Nominal.NPrf (.imp (.classMem Q (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q))))) := by
  let proofSupport : Finset Var := D.fv ∪ Q.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_Q : z ∉ Q.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (Q).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_Q, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elpw1 z Q D dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem Q (syn_cpw1 D)) (syn_wrex z D (.classEq Q (syn_csn (.cv z)))) p0000
  have p0002 :=
    @g_simpr (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))
  have p0003 :=
    @g_unieqd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) Q (syn_csn (.cv z)) p0002
  have p0004 :=
    @g_vex z
  have p0005 :=
    @g_unisn (.cv z) p0004
  have p0006 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv z))) (.cv z)) (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) p0005
  have p0007 :=
    @g_eqtrd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (syn_cuni Q) (syn_cuni (syn_csn (.cv z))) (.cv z) p0003 p0006
  have p0008 :=
    @g_simpl (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))
  have p0009 :=
    @g_eqeltrd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (syn_cuni Q) (.cv z) D p0007 p0008
  have p0010 :=
    @g_simpr (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))
  have p0011 :=
    @g_simpr (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))
  have p0012 :=
    @g_unieqd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) Q (syn_csn (.cv z)) p0011
  have p0013 :=
    @g_vex z
  have p0014 :=
    @g_unisn (.cv z) p0013
  have p0015 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv z))) (.cv z)) (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) p0014
  have p0016 :=
    @g_eqtrd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (syn_cuni Q) (syn_cuni (syn_csn (.cv z))) (.cv z) p0012 p0015
  have p0017 :=
    @g_eqcomd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (syn_cuni Q) (.cv z) p0016
  have p0018 :=
    @g_sneqd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (.cv z) (syn_cuni Q) p0017
  have p0019 :=
    @g_eqtrd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) Q (syn_csn (.cv z)) (syn_csn (syn_cuni Q)) p0010 p0018
  have p0020 :=
    @g_jca (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q))) p0009 p0019
  have p0021 :=
    @g_rexlimiva (.classEq Q (syn_csn (.cv z))) (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q)))) z D dv_cache_0003 p0020
  have p0022 :=
    @g_syl (.classMem Q (syn_cpw1 D)) (syn_wrex z D (.classEq Q (syn_csn (.cv z)))) (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q)))) p0001 p0021
  exact p0022

noncomputable def g_pw1descentf1odv
    (x : Var) (D : Class) (g : Var) (E : Class) (dv_D_x : x ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_g_x : g ≠ x) :
    Nominal.NPrf (.imp (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (syn_cmpt x D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) D E)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ ({g} : Finset Var) ∪ E.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_g : y ≠ g := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_y : g ≠ y :=
    Ne.symm fresh_y_ne_g
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, (Ne.symm dv_g_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, dv_E_x, (Ne.symm dv_g_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_not_E, fresh_y_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_eqid (syn_cmpt x D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))))
  have p0001 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D)
  have p0002 :=
    @g_f1of (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0003 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0001 p0002
  have p0004 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D)
  have p0005 :=
    @g_snelpw1 (.cv x) D
  have p0006 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D)) (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0004 p0005
  have p0007 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D)) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0003 p0006
  have p0008 :=
    @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv x)) (.cv g)
  have p0009 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D)) (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv x)) (syn_cpw1 D))) (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E)) p0007 p0008
  have p0010 :=
    @g_pw1argclcl E (syn_cfv (.cv g) (syn_csn (.cv x)))
  have p0011 :=
    @g_simpl (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))))
  have p0012 :=
    @g_syl (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E)) (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))))) (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E) p0010 p0011
  have p0013 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D)) (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E)) (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E) p0009 p0012
  have p0014 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)
  have p0015 :=
    @g_f1ocnv (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0016 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) p0014 p0015
  have p0017 :=
    @g_f1of (syn_cpw1 E) (syn_cpw1 D) (syn_ccnv (.cv g))
  have p0018 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)) (syn_wf1o (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) p0016 p0017
  have p0019 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)
  have p0020 :=
    @g_snelpw1 (.cv y) E
  have p0021 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)) (.classMem (.cv y) E) (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0019 p0020
  have p0022 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)) (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0018 p0021
  have p0023 :=
    @g_ffvelrn (syn_cpw1 E) (syn_cpw1 D) (syn_csn (.cv y)) (syn_ccnv (.cv g))
  have p0024 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)) (syn_wa (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) (.classMem (syn_csn (.cv y)) (syn_cpw1 E))) (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D)) p0022 p0023
  have p0025 :=
    @g_pw1argclcl D (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
  have p0026 :=
    @g_simpl (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))))
  have p0027 :=
    @g_syl (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))))) (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D) p0025 p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)) (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D)) (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D) p0024 p0027
  have p0029 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0030 :=
    @g_f1ocnv (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0031 :=
    @g_f1of (syn_cpw1 E) (syn_cpw1 D) (syn_ccnv (.cv g))
  have p0032 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) p0030 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) p0029 p0032
  have p0034 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0035 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0036 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0034 p0035
  have p0037 :=
    @g_snelpw1 (.cv y) E
  have p0038 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classMem (.cv y) E) (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0036 p0037
  have p0039 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0033 p0038
  have p0040 :=
    @g_ffvelrn (syn_cpw1 E) (syn_cpw1 D) (syn_csn (.cv y)) (syn_ccnv (.cv g))
  have p0041 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wa (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) (.classMem (syn_csn (.cv y)) (syn_cpw1 E))) (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D)) p0039 p0040
  have p0042 :=
    @g_pw1argclcl D (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
  have p0043 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))))
  have p0044 :=
    @g_syl (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))) p0042 p0043
  have p0045 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D)) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))) p0041 p0044
  have p0046 :=
    @g_eqeq1d (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))) (syn_csn (.cv x)) p0045
  have p0047 :=
    @g_fvex (syn_csn (.cv y)) (syn_ccnv (.cv g))
  have p0048 :=
    @g_uniex (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) p0047
  have p0049 :=
    @g_sneqb (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x) p0048
  have p0050 :=
    @g_a1i (syn_wb (.classEq (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))) (syn_csn (.cv x))) (.classEq (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x))) (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) p0049
  have p0051 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x))) (.classEq (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))) (syn_csn (.cv x))) (.classEq (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x)) p0046 p0050
  have p0052 :=
    @g_eqcom (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x)
  have p0053 :=
    @g_a1i (syn_wb (.classEq (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x)) (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))) (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) p0052
  have p0054 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x))) (.classEq (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x)) (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))) p0051 p0053
  have p0055 :=
    @g_bicomd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x))) (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))) p0054
  have p0056 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0057 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0058 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0059 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0057 p0058
  have p0060 :=
    @g_snelpw1 (.cv x) D
  have p0061 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0059 p0060
  have p0062 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0063 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0064 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0062 p0063
  have p0065 :=
    @g_snelpw1 (.cv y) E
  have p0066 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classMem (.cv y) E) (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0064 p0065
  have p0067 :=
    @g_n_3jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0056 p0061 p0066
  have p0068 :=
    @g_f1ocnvfvb (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv g)
  have p0069 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_w3a (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (syn_csn (.cv y)) (syn_cpw1 E))) (syn_wb (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y))) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x)))) p0067 p0068
  have p0070 :=
    @g_bicomd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y))) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x))) p0069
  have p0071 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))) (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y))) p0055 p0070
  have p0072 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0073 :=
    @g_f1of (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0074 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0072 p0073
  have p0075 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0076 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0077 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0075 p0076
  have p0078 :=
    @g_snelpw1 (.cv x) D
  have p0079 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0077 p0078
  have p0080 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0074 p0079
  have p0081 :=
    @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv x)) (.cv g)
  have p0082 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv x)) (syn_cpw1 D))) (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E)) p0080 p0081
  have p0083 :=
    @g_pw1argclcl E (syn_cfv (.cv g) (syn_csn (.cv x)))
  have p0084 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))))
  have p0085 :=
    @g_syl (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E)) (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))))) p0083 p0084
  have p0086 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E)) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))))) p0082 p0085
  have p0087 :=
    @g_eqeq1d (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) (syn_csn (.cv y)) p0086
  have p0088 :=
    @g_fvex (syn_csn (.cv x)) (.cv g)
  have p0089 :=
    @g_uniex (syn_cfv (.cv g) (syn_csn (.cv x))) p0088
  have p0090 :=
    @g_sneqb (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y) p0089
  have p0091 :=
    @g_a1i (syn_wb (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) (syn_csn (.cv y))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y))) (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) p0090
  have p0092 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y))) (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) (syn_csn (.cv y))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y)) p0087 p0091
  have p0093 :=
    @g_eqcom (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y)
  have p0094 :=
    @g_a1i (syn_wb (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y)) (.classEq (.cv y) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))))) (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) p0093
  have p0095 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y)) (.classEq (.cv y) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) p0092 p0094
  have p0096 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))) (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y))) (.classEq (.cv y) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) p0071 p0095
  have p0097 :=
    @g_f1o2d (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) x y D E (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (syn_cmpt x D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0000 p0013 p0028 p0096
  exact p0097

#print axioms g_pw1descentf1odv

end NFChoice.DirectNominalPrf.WPPReplay
