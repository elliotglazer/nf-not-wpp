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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk009StructuralPart030


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

noncomputable def g_n_0fin
     :
    Nominal.NPrf (.classMem (syn_c0) (syn_cfin)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_peano1
  have p0001 :=
    @g_eqid (syn_c0)
  have p0002 :=
    @g_el0c (syn_c0)
  have p0003 :=
    @g_mpbir (.classMem (syn_c0) (syn_c0c)) (.classEq (syn_c0) (syn_c0)) p0001 p0002
  have p0004 :=
    @g_eleq2 (.cv n) (syn_c0c) (syn_c0)
  have p0005 :=
    @g_rspcev (.classMem (syn_c0) (.cv n)) (.classMem (syn_c0) (syn_c0c)) n (syn_c0c) (syn_cnnc) (by exact (show n ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((Wff.classMem (syn_c0) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((syn_c0)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show n ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0004
  have p0006 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0) (syn_c0c)) (syn_wrex n (syn_cnnc) (.classMem (syn_c0) (.cv n))) p0000 p0003 p0005
  have p0007 :=
    @g_elfin n (syn_c0) (by exact (show n ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0008 :=
    @g_mpbir (.classMem (syn_c0) (syn_cfin)) (syn_wrex n (syn_cnnc) (.classMem (syn_c0) (.cv n))) p0006 p0007
  exact p0008



#print axioms g_n_0fin

end NFChoice.DirectNominalPrf.WPPReplay
