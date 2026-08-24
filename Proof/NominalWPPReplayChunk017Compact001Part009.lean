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
import NominalWPPReplayChunk017Compact001Part008

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

noncomputable def g_hnsiquomaprepvalndv
    (u : Var) (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_q_u : q ≠ u) (hyp_hnsiquomaprepvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0001 :=
    @g_hnsiquomapvalndv A q dv_cache_0001 hyp_hnsiquomaprepvalndv_1
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q))))) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0004 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0005 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0003 p0004
  have p0006 :=
    @g_pw1eq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) (.classEq (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A)))) p0005 p0006
  have p0008 :=
    @g_siecsnndv u (syn_chwniso A) dv_cache_0002
  have p0009 :=
    @g_eqcomi (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))) p0008
  have p0010 :=
    @g_a1i (.classEq (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0009
  have p0011 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))) p0007 p0010
  have p0012 :=
    @g_imaeq2d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_cpw1 (syn_cuni (.cv q))) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))) (syn_chnsicodemap A) p0011
  have p0013 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))) (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))) p0002 p0012
  have p0014 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0015 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (.cv u) (syn_chwcn A)) p0014 p0015
  have p0017 :=
    @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0018 :=
    @g_sylibr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0016 p0017
  have p0019 :=
    @g_hnsicodemapclassimcldndv A (syn_csn (.cv u)) hyp_hnsiquomaprepvalndv_1
  have p0020 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))) p0018 p0019
  have p0021 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) p0013 p0020
  exact p0021

noncomputable def g_hnordpw1repndv
    (u : Var) (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_q_u : q ≠ u) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classEq (.cv q) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ ({q} : Finset Var)
  have p0000 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0001 :=
    @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0002 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0006 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0005 p0006
  have p0008 :=
    @g_sneq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) (.classEq (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))) p0007 p0008
  have p0010 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))) p0004 p0009
  exact p0010

noncomputable def g_brsnsiandv
    (A : Class) (B : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wb (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B)) (syn_wbr A R B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    @g_id (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0)))
  have p0001 :=
    @g_sneq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0))
  have p0002 :=
    @g_syl (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (.classEq (syn_csn A) (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0)))) p0000 p0001
  have p0003 :=
    @g_breq1d (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csn A) (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csn B) (syn_csi R) p0002
  have p0004 :=
    @g_id (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0)))
  have p0005 :=
    @g_breq1d (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) A (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) B R p0004
  have p0006 :=
    @g_bibi12d (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B)) (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R) (syn_csn B)) (syn_wbr A R B) (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R B) p0003 p0005
  have p0007 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))
  have p0008 :=
    @g_sneq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0))
  have p0009 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0))) (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0))) (.classEq (syn_csn B) (syn_csn (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))) p0007 p0008
  have p0010 :=
    @g_breq2d (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0))) (syn_csn B) (syn_csn (syn_cif (.classMem B (syn_cvv)) B (syn_c0))) (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R) p0009
  have p0011 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))
  have p0012 :=
    @g_breq2d (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0))) B (syn_cif (.classMem B (syn_cvv)) B (syn_c0)) (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R p0011
  have p0013 :=
    @g_bibi12d (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0))) (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R) (syn_csn B)) (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R) (syn_csn (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))) (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R B) (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R (syn_cif (.classMem B (syn_cvv)) B (syn_c0))) p0010 p0012
  have p0014 :=
    @g_eqid (syn_c0)
  have p0015 :=
    @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem A (syn_cvv))
  have p0016 :=
    @g_n_0ex
  have p0017 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv)) (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem A (syn_cvv)))) p0016
  have p0018 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem A (syn_cvv)) A (syn_c0) (syn_cvv) p0015 p0017
  have p0019 :=
    Nominal.mp p0014 p0018
  have p0020 :=
    @g_eqid (syn_c0)
  have p0021 :=
    @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_cvv))
  have p0022 :=
    @g_n_0ex
  have p0023 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv)) (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem B (syn_cvv)))) p0022
  have p0024 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_cvv)) B (syn_c0) (syn_cvv) p0021 p0023
  have p0025 :=
    Nominal.mp p0020 p0024
  have p0026 :=
    @g_brsnsi (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) (syn_cif (.classMem B (syn_cvv)) B (syn_c0)) R p0019 p0025
  have p0027 :=
    @g_dedth2h (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B)) (syn_wbr A R B)) (syn_wb (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R) (syn_csn B)) (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R B)) (syn_wb (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R) (syn_csn (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))) (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))) A B (syn_c0) (syn_c0) p0006 p0013 p0026
  exact p0027

#print axioms g_brsnsiandv

end NFChoice.DirectNominalPrf.WPPReplay
