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
import NominalWPPReplayChunk009StructuralPart019


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

noncomputable def g_pw1eqadj
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) (hyp_pw1eqadj_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_pw1eqadj_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_wex x (syn_wex y (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y)))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_unieq (syn_cpw1 C) (syn_cun A (syn_csn B))
  have p0001 :=
    @g_unipw1 C
  have p0002 :=
    @g_uniun A (syn_csn B)
  have p0003 :=
    @g_n_3eqtr3g (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_cuni (syn_cpw1 C)) (syn_cuni (syn_cun A (syn_csn B))) C (syn_cun (syn_cuni A) (syn_cuni (syn_csn B))) p0000 p0001 p0002
  have p0004 :=
    @g_unisn B hyp_pw1eqadj_2
  have p0005 :=
    @g_pw1ss1c C
  have p0006 :=
    @g_ssun2 (syn_csn B) A
  have p0007 :=
    @g_snid B hyp_pw1eqadj_2
  have p0008 :=
    @g_sselii (syn_csn B) (syn_cun A (syn_csn B)) B p0006 p0007
  have p0009 :=
    @g_eleq2 (syn_cpw1 C) (syn_cun A (syn_csn B)) B
  have p0010 :=
    @g_mpbiri (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (.classMem B (syn_cpw1 C)) (.classMem B (syn_cun A (syn_csn B))) p0008 p0009
  have p0011 :=
    @g_sseldi (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_cpw1 C) (syn_c1c) B p0005 p0010
  have p0012 :=
    @g_el1c x B (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
  have p0013 :=
    @g_vex x
  have p0014 :=
    @g_unisn (.cv x) p0013
  have p0015 :=
    @g_sneqi (syn_cuni (syn_csn (.cv x))) (.cv x) p0014
  have p0016 :=
    @g_eqcomi (syn_csn (syn_cuni (syn_csn (.cv x)))) (syn_csn (.cv x)) p0015
  have p0017 :=
    @g_id (.classEq B (syn_csn (.cv x)))
  have p0018 :=
    @g_unieq B (syn_csn (.cv x))
  have p0019 :=
    @g_sneqd (.classEq B (syn_csn (.cv x))) (syn_cuni B) (syn_cuni (syn_csn (.cv x))) p0018
  have p0020 :=
    @g_n_3eqtr4a (.classEq B (syn_csn (.cv x))) (syn_csn (.cv x)) (syn_csn (syn_cuni (syn_csn (.cv x)))) B (syn_csn (syn_cuni B)) p0016 p0017 p0019
  have p0021 :=
    @g_exlimiv (.classEq B (syn_csn (.cv x))) (.classEq B (syn_csn (syn_cuni B))) x (by exact (show x ∉ ((Wff.classEq B (syn_csn (syn_cuni B)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((B).fv) ∪ (((syn_csn (syn_cuni B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact dv_B_x)) (show x ∉ ((syn_csn (syn_cuni B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (B).fv from (by exact dv_B_x))))))))))) p0020
  have p0022 :=
    @g_sylbi (.classMem B (syn_c1c)) (syn_wex x (.classEq B (syn_csn (.cv x)))) (.classEq B (syn_csn (syn_cuni B))) p0012 p0021
  have p0023 :=
    @g_syl (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (.classMem B (syn_c1c)) (.classEq B (syn_csn (syn_cuni B))) p0011 p0022
  have p0024 :=
    @g_syl5eq (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_cuni (syn_csn B)) B (syn_csn (syn_cuni B)) p0004 p0023
  have p0025 :=
    @g_uneq2d (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_cuni (syn_csn B)) (syn_csn (syn_cuni B)) (syn_cuni A) p0024
  have p0026 :=
    @g_eqtrd (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) C (syn_cun (syn_cuni A) (syn_cuni (syn_csn B))) (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))) p0003 p0025
  have p0027 :=
    @g_ssun1 A (syn_csn B)
  have p0028 :=
    @g_sseq2 (syn_cpw1 C) (syn_cun A (syn_csn B)) A
  have p0029 :=
    @g_mpbiri (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_wss A (syn_cpw1 C)) (syn_wss A (syn_cun A (syn_csn B))) p0027 p0028
  have p0030 :=
    @g_syl6ss (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) A (syn_cpw1 C) (syn_c1c) p0029 p0005
  have p0031 :=
    @g_eqpw1uni A
  have p0032 :=
    @g_syl (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_wss A (syn_c1c)) (.classEq A (syn_cpw1 (syn_cuni A))) p0030 p0031
  have p0033 :=
    @g_uniex A hyp_pw1eqadj_1
  have p0034 :=
    @g_uniex B hyp_pw1eqadj_2
  have p0035 :=
    @g_sneq (.cv y) (syn_cuni B)
  have p0036 :=
    @g_uneq12 (.cv x) (syn_cuni A) (syn_csn (.cv y)) (syn_csn (syn_cuni B))
  have p0037 :=
    @g_sylan2 (.classEq (.cv y) (syn_cuni B)) (.classEq (.cv x) (syn_cuni A)) (.classEq (syn_csn (.cv y)) (syn_csn (syn_cuni B))) (.classEq (syn_cun (.cv x) (syn_csn (.cv y))) (syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))) p0035 p0036
  have p0038 :=
    @g_eqeq2d (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B))) (syn_cun (.cv x) (syn_csn (.cv y))) (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))) C p0037
  have p0039 :=
    @g_pw1eq (.cv x) (syn_cuni A)
  have p0040 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cuni A)) (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni A)) A p0039
  have p0041 :=
    @g_adantr (.classEq (.cv x) (syn_cuni A)) (syn_wb (.classEq A (syn_cpw1 (.cv x))) (.classEq A (syn_cpw1 (syn_cuni A)))) (.classEq (.cv y) (syn_cuni B)) p0040
  have p0042 :=
    @g_eqeq2d (.classEq (.cv y) (syn_cuni B)) (syn_csn (.cv y)) (syn_csn (syn_cuni B)) B p0035
  have p0043 :=
    @g_adantl (.classEq (.cv y) (syn_cuni B)) (syn_wb (.classEq B (syn_csn (.cv y))) (.classEq B (syn_csn (syn_cuni B)))) (.classEq (.cv x) (syn_cuni A)) p0042
  have p0044 :=
    @g_n_3anbi123d (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B))) (.classEq C (syn_cun (.cv x) (syn_csn (.cv y)))) (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))) (.classEq A (syn_cpw1 (.cv x))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_csn (.cv y))) (.classEq B (syn_csn (syn_cuni B))) p0038 p0041 p0043
  have p0045 :=
    @g_spc2ev (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y)))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y)))) (syn_w3a (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_csn (syn_cuni B)))) x y (syn_cuni A) (syn_cuni B) (by exact (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact dv_A_x))))) (by exact (show y ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (A).fv from (by exact dv_A_y))))) (by exact (show x ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (B).fv from (by exact dv_B_x))))) (by exact (show y ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (B).fv from (by exact dv_B_y))))) (by exact (show x ∉ ((syn_w3a (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_csn (syn_cuni B))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show x ∉ (((Wff.classEq B (syn_csn (syn_cuni B)))).fv) ∪ (((Wff.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))).fv) ∪ (((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classEq B (syn_csn (syn_cuni B)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((B).fv) ∪ (((syn_csn (syn_cuni B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact dv_B_x)) (show x ∉ ((syn_csn (syn_cuni B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (B).fv from (by exact dv_B_x)))))))))) (show x ∉ ((Wff.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((C).fv) ∪ (((syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact dv_C_x)) (show x ∉ ((syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ (((syn_cuni A)).fv) ∪ (((syn_csn (syn_cuni B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact dv_A_x)))) (show x ∉ ((syn_csn (syn_cuni B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (B).fv from (by exact dv_B_x))))))))))))))) (show x ∉ ((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((syn_cpw1 (syn_cuni A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cpw1 (syn_cuni A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact dv_A_x))))))))))))))) (by exact (show y ∉ ((syn_w3a (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_csn (syn_cuni B))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show y ∉ (((Wff.classEq B (syn_csn (syn_cuni B)))).fv) ∪ (((Wff.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))).fv) ∪ (((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classEq B (syn_csn (syn_cuni B)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((B).fv) ∪ (((syn_csn (syn_cuni B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact dv_B_y)) (show y ∉ ((syn_csn (syn_cuni B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (B).fv from (by exact dv_B_y)))))))))) (show y ∉ ((Wff.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((C).fv) ∪ (((syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact dv_C_y)) (show y ∉ ((syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show y ∉ (((syn_cuni A)).fv) ∪ (((syn_csn (syn_cuni B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (A).fv from (by exact dv_A_y)))) (show y ∉ ((syn_csn (syn_cuni B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (B).fv from (by exact dv_B_y))))))))))))))) (show y ∉ ((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ (((syn_cpw1 (syn_cuni A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact dv_A_y)) (show y ∉ ((syn_cpw1 (syn_cuni A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (A).fv from (by exact dv_A_y))))))))))))))) (show x ≠ y from (by exact dv_x_y)) p0033 p0034 p0044
  have p0046 :=
    @g_syl3anc (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B)))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_csn (syn_cuni B))) (syn_wex x (syn_wex y (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y)))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y)))))) p0026 p0032 p0023 p0045
  have p0047 :=
    @g_pw1un (.cv x) (syn_csn (.cv y))
  have p0048 :=
    @g_vex y
  have p0049 :=
    @g_pw1sn (.cv y) p0048
  have p0050 :=
    @g_uneq2i (syn_cpw1 (syn_csn (.cv y))) (syn_csn (syn_csn (.cv y))) (syn_cpw1 (.cv x)) p0049
  have p0051 :=
    @g_eqtri (syn_cpw1 (syn_cun (.cv x) (syn_csn (.cv y)))) (syn_cun (syn_cpw1 (.cv x)) (syn_cpw1 (syn_csn (.cv y)))) (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y)))) p0047 p0050
  have p0052 :=
    @g_pw1eq C (syn_cun (.cv x) (syn_csn (.cv y)))
  have p0053 :=
    @g_sneq B (syn_csn (.cv y))
  have p0054 :=
    @g_uneq12 A (syn_cpw1 (.cv x)) (syn_csn B) (syn_csn (syn_csn (.cv y)))
  have p0055 :=
    @g_sylan2 (.classEq B (syn_csn (.cv y))) (.classEq A (syn_cpw1 (.cv x))) (.classEq (syn_csn B) (syn_csn (syn_csn (.cv y)))) (.classEq (syn_cun A (syn_csn B)) (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y))))) p0053 p0054
  have p0056 :=
    @g_eqeqan12d (.classEq C (syn_cun (.cv x) (syn_csn (.cv y)))) (syn_wa (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y)))) (syn_cpw1 C) (syn_cpw1 (syn_cun (.cv x) (syn_csn (.cv y)))) (syn_cun A (syn_csn B)) (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y)))) p0052 p0055
  have p0057 :=
    @g_n_3impb (.classEq C (syn_cun (.cv x) (syn_csn (.cv y)))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y))) (syn_wb (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (.classEq (syn_cpw1 (syn_cun (.cv x) (syn_csn (.cv y)))) (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y)))))) p0056
  have p0058 :=
    @g_mpbiri (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y)))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y)))) (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (.classEq (syn_cpw1 (syn_cun (.cv x) (syn_csn (.cv y)))) (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y))))) p0051 p0057
  have p0059 :=
    @g_exlimivv (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y)))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y)))) (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) x y (by exact (show x ∉ ((Wff.classEq (syn_cpw1 C) (syn_cun A (syn_csn B)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_cpw1 C)).fv) ∪ (((syn_cun A (syn_csn B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cpw1 C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (C).fv from (by exact dv_C_x)))) (show x ∉ ((syn_cun A (syn_csn B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ ((A).fv) ∪ (((syn_csn B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (B).fv from (by exact dv_B_x))))))))))))) (by exact (show y ∉ ((Wff.classEq (syn_cpw1 C) (syn_cun A (syn_csn B)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((syn_cpw1 C)).fv) ∪ (((syn_cun A (syn_csn B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cpw1 C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ (C).fv from (by exact dv_C_y)))) (show y ∉ ((syn_cun A (syn_csn B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show y ∉ ((A).fv) ∪ (((syn_csn B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact dv_A_y)) (show y ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (B).fv from (by exact dv_B_y))))))))))))) p0058
  have p0060 :=
    @g_impbii (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_wex x (syn_wex y (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y)))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y)))))) p0046 p0059
  exact p0060

noncomputable def g_sspw1
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_sspw1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_cpw1 B)) (syn_wex x (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_uniss A (syn_cpw1 B)
  have p0001 :=
    @g_unipw1 B
  have p0002 :=
    @g_syl6sseq (syn_wss A (syn_cpw1 B)) (syn_cuni A) (syn_cuni (syn_cpw1 B)) B p0000 p0001
  have p0003 :=
    @g_pw1ss1c B
  have p0004 :=
    @g_sstr A (syn_cpw1 B) (syn_c1c)
  have p0005 :=
    @g_mpan2 (syn_wss A (syn_cpw1 B)) (syn_wss (syn_cpw1 B) (syn_c1c)) (syn_wss A (syn_c1c)) p0003 p0004
  have p0006 :=
    @g_eqpw1uni A
  have p0007 :=
    @g_syl (syn_wss A (syn_cpw1 B)) (syn_wss A (syn_c1c)) (.classEq A (syn_cpw1 (syn_cuni A))) p0005 p0006
  have p0008 :=
    @g_uniex A hyp_sspw1_1
  have p0009 :=
    @g_sseq1 (.cv x) (syn_cuni A) B
  have p0010 :=
    @g_pw1eq (.cv x) (syn_cuni A)
  have p0011 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cuni A)) (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni A)) A p0010
  have p0012 :=
    @g_anbi12d (.classEq (.cv x) (syn_cuni A)) (syn_wss (.cv x) B) (syn_wss (syn_cuni A) B) (.classEq A (syn_cpw1 (.cv x))) (.classEq A (syn_cpw1 (syn_cuni A))) p0009 p0011
  have p0013 :=
    @g_spcev (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x)))) (syn_wa (syn_wss (syn_cuni A) B) (.classEq A (syn_cpw1 (syn_cuni A)))) x (syn_cuni A) (by exact (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact dv_A_x))))) (by exact (show x ∉ ((syn_wa (syn_wss (syn_cuni A) B) (.classEq A (syn_cpw1 (syn_cuni A))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((syn_wss (syn_cuni A) B)).fv) ∪ (((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wss (syn_cuni A) B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show x ∉ (((syn_cuni A)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact dv_A_x)))) (show x ∉ (B).fv from (by exact dv_B_x)))))) (show x ∉ ((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((syn_cpw1 (syn_cuni A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cpw1 (syn_cuni A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact dv_A_x))))))))))))))) p0008 p0012
  have p0014 :=
    @g_syl2anc (syn_wss A (syn_cpw1 B)) (syn_wss (syn_cuni A) B) (.classEq A (syn_cpw1 (syn_cuni A))) (syn_wex x (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x))))) p0002 p0007 p0013
  have p0015 :=
    @g_pw1ss (.cv x) B
  have p0016 :=
    @g_sseq1 A (syn_cpw1 (.cv x)) (syn_cpw1 B)
  have p0017 :=
    @g_syl5ibr (syn_wss (.cv x) B) (syn_wss A (syn_cpw1 B)) (.classEq A (syn_cpw1 (.cv x))) (syn_wss (syn_cpw1 (.cv x)) (syn_cpw1 B)) p0015 p0016
  have p0018 :=
    @g_impcom (.classEq A (syn_cpw1 (.cv x))) (syn_wss (.cv x) B) (syn_wss A (syn_cpw1 B)) p0017
  have p0019 :=
    @g_exlimiv (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x)))) (syn_wss A (syn_cpw1 B)) x (by exact (show x ∉ ((syn_wss A (syn_cpw1 B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show x ∉ ((A).fv) ∪ (((syn_cpw1 B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (B).fv from (by exact dv_B_x))))))))) p0018
  have p0020 :=
    @g_impbii (syn_wss A (syn_cpw1 B)) (syn_wex x (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x))))) p0014 p0019
  exact p0020

noncomputable def g_dfiota2
    (ph : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cio x ph) (syn_cuni (.cab y (.all x (syn_wb ph (.objEq x y)))))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota ph x y (by exact (show y ∉ (ph).fv from (by exact dv_ph_y))) (show x ≠ y from (by exact dv_x_y))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x (.cv y) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y)))))))
  have p0002_e00_recanon : Nominal.NPrf (.classEq (syn_csn (.cv y)) (.cab x (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0001
  have p0002 :=
    @g_eqeq2i (syn_csn (.cv y)) (.cab x (.objEq x y)) (.cab x ph) p0002_e00_recanon
  have p0003 :=
    @g_abbib ph (.objEq x y) x
  have p0004 :=
    @g_bitri (.classEq (.cab x ph) (syn_csn (.cv y))) (.classEq (.cab x ph) (.cab x (.objEq x y))) (.all x (syn_wb ph (.objEq x y))) p0002 p0003
  have p0005 :=
    @g_abbii (.classEq (.cab x ph) (syn_csn (.cv y))) (.all x (syn_wb ph (.objEq x y))) y p0004
  have p0006 :=
    @g_unieqi (.cab y (.classEq (.cab x ph) (syn_csn (.cv y)))) (.cab y (.all x (syn_wb ph (.objEq x y)))) p0005
  have p0007 :=
    @g_eqtri (syn_cio x ph) (syn_cuni (.cab y (.classEq (.cab x ph) (syn_csn (.cv y))))) (syn_cuni (.cab y (.all x (syn_wb ph (.objEq x y))))) p0000 p0006
  exact p0007

noncomputable def g_nfiota1
    (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wnfc x (syn_cio x ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_dfiota2 ph x y (by exact (show y ∉ (ph).fv from (by exact fresh_y_not_ph))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 :=
    @g_nfaba1 (syn_wb ph (.classEq (.cv x) (.cv y))) x y
  have p0002 :=
    @g_nfuni x (.cab y (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))) p0001
  have p0003_e00_recanon : Nominal.NPrf (.classEq (syn_cio x ph) (syn_cuni (.cab y (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cio syn_cuni syn_wex syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.classMem
            ·
              exact Nominal.RecanonTransportDev.TRecanonClass.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonClass.cab
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0003 :=
    @g_nfcxfr x (syn_cio x ph) (syn_cuni (.cab y (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))))) p0003_e00_recanon p0002
  exact p0003

noncomputable def g_iotabi
    (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (syn_wb ph ps)) (.classEq (syn_cio x ph) (syn_cio x ps))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have p0000 :=
    @g_abbib ph ps x
  have p0001 :=
    @g_biimpri (.classEq (.cab x ph) (.cab x ps)) (.all x (syn_wb ph ps)) p0000
  have p0002 :=
    @g_eqeq1d (.all x (syn_wb ph ps)) (.cab x ph) (.cab x ps) (syn_csn (.cv z)) p0001
  have p0003 :=
    @g_abbidv (.all x (syn_wb ph ps)) (.classEq (.cab x ph) (syn_csn (.cv z))) (.classEq (.cab x ps) (syn_csn (.cv z))) z (by exact (show z ∉ ((Wff.all x (syn_wb ph ps))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show z ∉ (((syn_wb ph ps)).fv).erase x from (fun hmem => (show z ∉ ((syn_wb ph ps)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show z ∉ ((ph).fv) ∪ ((ps).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (ph).fv from (by exact fresh_z_not_ph)) (show z ∉ (ps).fv from (by exact fresh_z_not_ps)))))) (Finset.mem_of_mem_erase hmem)))))) p0002
  have p0004 :=
    @g_unieqd (.all x (syn_wb ph ps)) (.cab z (.classEq (.cab x ph) (syn_csn (.cv z)))) (.cab z (.classEq (.cab x ps) (syn_csn (.cv z)))) p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota ph x z (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph))) (show x ≠ z from (by exact fresh_x_ne_z))
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota ps x z (by exact (show z ∉ (ps).fv from (by exact fresh_z_not_ps))) (show x ≠ z from (by exact fresh_x_ne_z))
  have p0007 :=
    @g_n_3eqtr4g (.all x (syn_wb ph ps)) (syn_cuni (.cab z (.classEq (.cab x ph) (syn_csn (.cv z))))) (syn_cuni (.cab z (.classEq (.cab x ps) (syn_csn (.cv z))))) (syn_cio x ph) (syn_cio x ps) p0004 p0005 p0006
  exact p0007

noncomputable def g_uniabio
    (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.all x (syn_wb ph (.objEq x y))) (.classEq (syn_cuni (.cab x ph)) (.cv y))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  have p0000 :=
    @g_abbib ph (.objEq x y) x
  have p0001 :=
    @g_biimpri (.classEq (.cab x ph) (.cab x (.objEq x y))) (.all x (syn_wb ph (.objEq x y))) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x (.cv y) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y)))))))
  have p0003_e01_recanon : Nominal.NPrf (.classEq (syn_csn (.cv y)) (.cab x (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0002
  have p0003 :=
    @g_syl6eqr (.all x (syn_wb ph (.objEq x y))) (.cab x ph) (.cab x (.objEq x y)) (syn_csn (.cv y)) p0001 p0003_e01_recanon
  have p0004 :=
    @g_unieqd (.all x (syn_wb ph (.objEq x y))) (.cab x ph) (syn_csn (.cv y)) p0003
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_unisn (.cv y) p0005
  have p0007 :=
    @g_syl6eq (.all x (syn_wb ph (.objEq x y))) (syn_cuni (.cab x ph)) (syn_cuni (syn_csn (.cv y))) (.cv y) p0004 p0006
  exact p0007

noncomputable def g_iotaval
    (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) (.classEq (syn_cio x ph) (.cv y))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have p0000 :=
    @g_dfiota2 ph x z (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph))) (show x ≠ z from (by exact fresh_x_ne_z))
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_sbeqalb ph x (.cv y) (.cv z) (syn_cvv) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y))))))) (by exact (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))))
  have p0003 :=
    @g_equcomi y z
  have p0004_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (.cv z)) (.classEq (.cv z) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0003
  have p0004 :=
    @g_syl6 (.classMem (.cv y) (syn_cvv)) (syn_wa (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))) (.classEq (.cv y) (.cv z)) (.classEq (.cv z) (.cv y)) p0002 p0004_e01_recanon
  have p0005 :=
    Nominal.mp p0001 p0004
  have p0006 :=
    @g_ex (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)) p0005
  have p0007 :=
    @g_equequ2 y z x
  have p0008_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (.cv z)) (syn_wb (.classEq (.cv x) (.cv y)) (.classEq (.cv x) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0007
  have p0008 :=
    @g_eqcoms (syn_wb (.classEq (.cv x) (.cv y)) (.classEq (.cv x) (.cv z))) (.cv y) (.cv z) p0008_e00_recanon
  have p0009 :=
    @g_bibi2d (.classEq (.cv z) (.cv y)) (.classEq (.cv x) (.cv y)) (.classEq (.cv x) (.cv z)) ph p0008
  have p0010 :=
    @g_biimpd (.classEq (.cv z) (.cv y)) (syn_wb ph (.classEq (.cv x) (.cv y))) (syn_wb ph (.classEq (.cv x) (.cv z))) p0009
  have p0011 :=
    @g_alimdv (.classEq (.cv z) (.cv y)) (syn_wb ph (.classEq (.cv x) (.cv y))) (syn_wb ph (.classEq (.cv x) (.cv z))) x (by exact (show x ∉ ((Wff.classEq (.cv z) (.cv y))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv z)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y))))))))))) p0010
  have p0012 :=
    @g_com12 (.classEq (.cv z) (.cv y)) (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) p0011
  have p0013 :=
    @g_impbid (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)) p0006 p0012
  have p0014 :=
    @g_alrimiv (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) (syn_wb (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y))) z (by exact (show z ∉ ((Wff.all x (syn_wb ph (.classEq (.cv x) (.cv y))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show z ∉ (((syn_wb ph (.classEq (.cv x) (.cv y)))).fv).erase x from (fun hmem => (show z ∉ ((syn_wb ph (.classEq (.cv x) (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show z ∉ ((ph).fv) ∪ (((Wff.classEq (.cv x) (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (ph).fv from (by exact fresh_z_not_ph)) (show z ∉ ((Wff.classEq (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))))) (Finset.mem_of_mem_erase hmem)))))) p0013
  have p0015 :=
    @g_uniabio (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) z y (show z ≠ y from (by exact fresh_z_ne_y))
  have p0016_e01_recanon : Nominal.NPrf (.imp (.all z (syn_wb (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)))) (.classEq (syn_cuni (.cab z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0015
  have p0016 :=
    @g_syl (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) (.all z (syn_wb (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)))) (.classEq (syn_cuni (.cab z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) (.cv y)) p0014 p0016_e01_recanon
  have p0017_e00_recanon : Nominal.NPrf (.classEq (syn_cio x ph) (syn_cuni (.cab z (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cio syn_cuni syn_wex syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.classMem
            ·
              exact Nominal.RecanonTransportDev.TRecanonClass.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonClass.cab
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0017 :=
    @g_syl5eq (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) (syn_cio x ph) (syn_cuni (.cab z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) (.cv y) p0017_e00_recanon p0016
  exact p0017

noncomputable def g_iota1
    (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_weu x ph) (syn_wb ph (.classEq (syn_cio x ph) (.cv x)))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have p0000 :=
    Nominal.dfEu x z ph (show x ≠ z from (by exact fresh_x_ne_z)) (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
  have p0001 :=
    @g_sp (syn_wb ph (.classEq (.cv x) (.cv z))) x
  have p0002 :=
    @g_iotaval ph x z (show x ≠ z from (by exact fresh_x_ne_z))
  have p0003 :=
    @g_eqeq2d (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (syn_cio x ph) (.cv z) (.cv x) p0002
  have p0004 :=
    @g_bitr4d (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) ph (.classEq (.cv x) (.cv z)) (.classEq (.cv x) (syn_cio x ph)) p0001 p0003
  have p0005 :=
    @g_eqcom (.cv x) (syn_cio x ph)
  have p0006 :=
    @g_syl6bb (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) ph (.classEq (.cv x) (syn_cio x ph)) (.classEq (syn_cio x ph) (.cv x)) p0004 p0005
  have p0007 :=
    @g_exlimiv (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (syn_wb ph (.classEq (syn_cio x ph) (.cv x))) z (by exact (show z ∉ ((syn_wb ph (.classEq (syn_cio x ph) (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show z ∉ ((ph).fv) ∪ (((Wff.classEq (syn_cio x ph) (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (ph).fv from (by exact fresh_z_not_ph)) (show z ∉ ((Wff.classEq (syn_cio x ph) (.cv x))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((syn_cio x ph)).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cio x ph)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio]; exact (show z ∉ ((ph).fv).erase x from (fun hmem => (show z ∉ (ph).fv from (by exact fresh_z_not_ph)) (Finset.mem_of_mem_erase hmem))))) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))))))))))) p0006
  have p0008_e00_recanon : Nominal.NPrf (syn_wb (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0008 :=
    @g_sylbi (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))) (syn_wb ph (.classEq (syn_cio x ph) (.cv x))) p0008_e00_recanon p0007
  exact p0008

noncomputable def g_iotanul
    (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.neg (syn_weu x ph)) (.classEq (syn_cio x ph) (syn_c0))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have p0000 :=
    Nominal.dfEu x z ph (show x ≠ z from (by exact fresh_x_ne_z)) (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
  have p0001 :=
    @g_dfiota2 ph x z (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph))) (show x ≠ z from (by exact fresh_x_ne_z))
  have p0002 :=
    @g_alnex (.all x (syn_wb ph (.objEq x z))) z
  have p0003 :=
    Nominal.ax1 (.neg (.all x (syn_wb ph (.objEq x z)))) (.objEq z z)
  have p0004 :=
    @g_eqidd (.neg (.all x (syn_wb ph (.objEq x z)))) (.cv z)
  have p0005_e01_recanon : Nominal.NPrf (.imp (.neg (.all x (syn_wb ph (.objEq x z)))) (.objEq z z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0004
  have p0005 :=
    @g_impbid1 (.neg (.all x (syn_wb ph (.objEq x z)))) (.objEq z z) (.neg (.all x (syn_wb ph (.objEq x z)))) p0003 p0005_e01_recanon
  have p0006 :=
    @g_con2bid (.neg (.all x (syn_wb ph (.objEq x z)))) (.objEq z z) (.all x (syn_wb ph (.objEq x z))) p0005
  have p0007 :=
    @g_alimi (.neg (.all x (syn_wb ph (.objEq x z)))) (syn_wb (.all x (syn_wb ph (.objEq x z))) (.neg (.objEq z z))) z p0006
  have p0008 :=
    @g_abbib (.all x (syn_wb ph (.objEq x z))) (.neg (.objEq z z)) z
  have p0009 :=
    @g_sylibr (.all z (.neg (.all x (syn_wb ph (.objEq x z))))) (.all z (syn_wb (.all x (syn_wb ph (.objEq x z))) (.neg (.objEq z z)))) (.classEq (.cab z (.all x (syn_wb ph (.objEq x z)))) (.cab z (.neg (.objEq z z)))) p0007 p0008
  have p0010 :=
    @g_dfnul2 z
  have p0011_e01_recanon : Nominal.NPrf (.classEq (syn_c0) (.cab z (.neg (.objEq z z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0010
  have p0011 :=
    @g_syl6eqr (.all z (.neg (.all x (syn_wb ph (.objEq x z))))) (.cab z (.all x (syn_wb ph (.objEq x z)))) (.cab z (.neg (.objEq z z))) (syn_c0) p0009 p0011_e01_recanon
  have p0012 :=
    @g_sylbir (.neg (syn_wex z (.all x (syn_wb ph (.objEq x z))))) (.all z (.neg (.all x (syn_wb ph (.objEq x z))))) (.classEq (.cab z (.all x (syn_wb ph (.objEq x z)))) (syn_c0)) p0002 p0011
  have p0013 :=
    @g_unieqd (.neg (syn_wex z (.all x (syn_wb ph (.objEq x z))))) (.cab z (.all x (syn_wb ph (.objEq x z)))) (syn_c0) p0012
  have p0014 :=
    @g_uni0
  have p0015 :=
    @g_syl6eq (.neg (syn_wex z (.all x (syn_wb ph (.objEq x z))))) (syn_cuni (.cab z (.all x (syn_wb ph (.objEq x z))))) (syn_cuni (syn_c0)) (syn_c0) p0013 p0014
  have p0016 :=
    @g_syl5eq (.neg (syn_wex z (.all x (syn_wb ph (.objEq x z))))) (syn_cio x ph) (syn_cuni (.cab z (.all x (syn_wb ph (.objEq x z))))) (syn_c0) p0001 p0015
  have p0017 :=
    @g_sylnbi (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.objEq x z)))) (.classEq (syn_cio x ph) (syn_c0)) p0000 p0016
  exact p0017

noncomputable def g_iotaex
    (ph : Wff) (x : Var) :
    Nominal.NPrf (.classMem (syn_cio x ph) (syn_cvv)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have p0000 :=
    @g_iotaval ph x z (show x ≠ z from (by exact fresh_x_ne_z))
  have p0001 :=
    @g_eqcomd (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (syn_cio x ph) (.cv z) p0000
  have p0002 :=
    @g_eximi (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (syn_cio x ph)) z p0001
  have p0003 :=
    Nominal.dfEu x z ph (show x ≠ z from (by exact fresh_x_ne_z)) (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
  have p0004 :=
    @g_isset z (syn_cio x ph) (by exact (show z ∉ ((syn_cio x ph)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio]; exact (show z ∉ ((ph).fv).erase x from (fun hmem => (show z ∉ (ph).fv from (by exact fresh_z_not_ph)) (Finset.mem_of_mem_erase hmem))))))
  have p0005_e01_recanon : Nominal.NPrf (syn_wb (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0005 :=
    @g_n_3imtr4i (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))) (syn_wex z (.classEq (.cv z) (syn_cio x ph))) (syn_weu x ph) (.classMem (syn_cio x ph) (syn_cvv)) p0002 p0005_e01_recanon p0004
  have p0006 :=
    @g_iotanul ph x
  have p0007 :=
    @g_n_0ex
  have p0008 :=
    @g_syl6eqel (.neg (syn_weu x ph)) (syn_cio x ph) (syn_c0) (syn_cvv) p0006 p0007
  have p0009 :=
    @g_pm2_61i (syn_weu x ph) (.classMem (syn_cio x ph) (syn_cvv)) p0005 p0008
  exact p0009



#print axioms g_iotaex

end NFChoice.DirectNominalPrf.WPPReplay
