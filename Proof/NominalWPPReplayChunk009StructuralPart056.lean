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
import NominalWPPReplayChunk009StructuralPart055


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

noncomputable def g_tfindi
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne (syn_cplc M N) (syn_c0))) (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_not_M : c ∉ M.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (h))
  have fresh_c_not_N : c ∉ N.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have p0000 :=
    @g_n0 a (syn_cplc M N) (by exact (show a ∉ ((syn_cplc M N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ (N).fv from (by exact fresh_a_not_N)))))))
  have p0001 :=
    @g_nncaddccl M N
  have p0002 :=
    @g_tfincl (syn_cplc M N)
  have p0003 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (syn_cplc M N) (syn_cnnc)) (.classMem (syn_ctfin (syn_cplc M N)) (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (syn_ctfin (syn_cplc M N)) (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N)) p0003
  have p0005 :=
    @g_tfincl M
  have p0006 :=
    @g_tfincl N
  have p0007 :=
    @g_nncaddccl (syn_ctfin M) (syn_ctfin N)
  have p0008 :=
    @g_syl2an (.classMem M (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) (.classMem (syn_cplc (syn_ctfin M) (syn_ctfin N)) (syn_cnnc)) (.classMem N (syn_cnnc)) p0005 p0006 p0007
  have p0009 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (syn_cplc (syn_ctfin M) (syn_ctfin N)) (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N)) p0008
  have p0010 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (syn_cplc M N) (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N)) p0001
  have p0011 :=
    @g_simp3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N))
  have p0012 :=
    @g_tfinpw1 (.cv a) (syn_cplc M N)
  have p0013 :=
    @g_syl2anc (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N))) (.classMem (syn_cplc M N) (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc M N))) p0010 p0011 p0012
  have p0014 :=
    @g_eladdc (.cv a) M N b c (by exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a))))))) (by exact (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a))))))) (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) (by exact (show c ∉ (M).fv from (by exact fresh_c_not_M))) (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N))) (by exact (show c ∉ (N).fv from (by exact fresh_c_not_N))) (show b ≠ c from (by exact fresh_b_ne_c))
  have p0015 :=
    @g_simplll (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0016 :=
    @g_simplrl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (.cv b) M) (.classMem (.cv c) N) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0017 :=
    @g_tfinpw1 (.cv b) M
  have p0018 :=
    @g_syl2anc (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N))) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))) (.classMem M (syn_cnnc)) (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) p0015 p0016 p0017
  have p0019 :=
    @g_simpllr (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0020 :=
    @g_simplrr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (.cv b) M) (.classMem (.cv c) N) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0021 :=
    @g_tfinpw1 (.cv c) N
  have p0022 :=
    @g_syl2anc (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N))) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))) (.classMem N (syn_cnnc)) (.classMem (.cv c) N) (.classMem (syn_cpw1 (.cv c)) (syn_ctfin N)) p0019 p0020 p0021
  have p0023 :=
    @g_pw1eq (syn_cin (.cv b) (.cv c)) (syn_c0)
  have p0024 :=
    @g_pw1in (.cv b) (.cv c)
  have p0025 :=
    @g_pw10
  have p0026 :=
    @g_n_3eqtr3g (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_cpw1 (syn_cin (.cv b) (.cv c))) (syn_cpw1 (syn_c0)) (syn_cin (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) (syn_c0) p0023 p0024 p0025
  have p0027 :=
    @g_adantl (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (syn_cin (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) (syn_c0)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N))) p0026
  have p0028 :=
    @g_eladdci (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c)) (syn_ctfin M) (syn_ctfin N)
  have p0029 :=
    @g_syl3anc (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N))) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv c)) (syn_ctfin N)) (.classEq (syn_cin (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) (syn_c0)) (.classMem (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0018 p0022 p0027 p0028
  have p0030 :=
    @g_pw1eq (.cv a) (syn_cun (.cv b) (.cv c))
  have p0031 :=
    @g_pw1un (.cv b) (.cv c)
  have p0032 :=
    @g_syl6eq (.classEq (.cv a) (syn_cun (.cv b) (.cv c))) (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cun (.cv b) (.cv c))) (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) p0030 p0031
  have p0033 :=
    @g_eleq1d (.classEq (.cv a) (syn_cun (.cv b) (.cv c))) (syn_cpw1 (.cv a)) (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) (syn_cplc (syn_ctfin M) (syn_ctfin N)) p0032
  have p0034 :=
    @g_syl5ibrcom (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N))) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) (.classEq (.cv a) (syn_cun (.cv b) (.cv c))) (.classMem (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0029 p0033
  have p0035 :=
    @g_expimpd (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N))) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv a) (syn_cun (.cv b) (.cv c))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0034
  have p0036 :=
    @g_rexlimdvva (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) b c M N (by exact (show c ∉ (M).fv from (by exact fresh_c_not_M))) (by exact (show b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_cplc (syn_ctfin M) (syn_ctfin N))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))))) (show b ∉ ((syn_cplc (syn_ctfin M) (syn_ctfin N))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((syn_ctfin M)).fv) ∪ (((syn_ctfin N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))) (show b ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show b ∉ (N).fv from (by exact fresh_b_not_N))))))))))))) (by exact (show c ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_cplc (syn_ctfin M) (syn_ctfin N))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))))) (show c ∉ ((syn_cplc (syn_ctfin M) (syn_ctfin N))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show c ∉ (((syn_ctfin M)).fv) ∪ (((syn_ctfin N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show c ∉ (M).fv from (by exact fresh_c_not_M)))) (show c ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show c ∉ (N).fv from (by exact fresh_c_not_N))))))))))))) (by exact (show b ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (M).fv from (by exact fresh_b_not_M)) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (N).fv from (by exact fresh_b_not_N)) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show c ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show c ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ (M).fv from (by exact fresh_c_not_M)) (show c ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show c ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ (N).fv from (by exact fresh_c_not_N)) (show c ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show b ≠ c from (by exact fresh_b_ne_c)) p0035
  have p0037 :=
    @g_syl5bi (.classMem (.cv a) (syn_cplc M N)) (syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))))) (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0014 p0036
  have p0038 :=
    @g_n_3impia (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N)) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0037
  have p0039 :=
    @g_nnceleq (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))
  have p0040 :=
    @g_syl22anc (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N))) (.classMem (syn_ctfin (syn_cplc M N)) (syn_cnnc)) (.classMem (syn_cplc (syn_ctfin M) (syn_ctfin N)) (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc M N))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0004 p0009 p0013 p0038 p0039
  have p0041 :=
    @g_n_3expia (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N)) (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0040
  have p0042 :=
    @g_exlimdv (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (.cv a) (syn_cplc M N)) (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) a (by exact (show a ∉ ((Wff.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_ctfin (syn_cplc M N))).fv) ∪ (((syn_cplc (syn_ctfin M) (syn_ctfin N))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_ctfin (syn_cplc M N))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show a ∉ ((syn_cplc M N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ (N).fv from (by exact fresh_a_not_N)))))))) (show a ∉ ((syn_cplc (syn_ctfin M) (syn_ctfin N))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ (((syn_ctfin M)).fv) ∪ (((syn_ctfin N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_ctfin M)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))) (show a ∉ ((syn_ctfin N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show a ∉ (N).fv from (by exact fresh_a_not_N))))))))))))) (by exact (show a ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((Wff.classMem N (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.classMem N (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((N).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (N).fv from (by exact fresh_a_not_N)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0041
  have p0043 :=
    @g_syl5bi (syn_wne (syn_cplc M N) (syn_c0)) (syn_wex a (.classMem (.cv a) (syn_cplc M N))) (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0000 p0042
  have p0044 :=
    @g_n_3impia (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0043
  exact p0044

noncomputable def g_tfin0c
     :
    Nominal.NPrf (.classEq (syn_ctfin (syn_c0c)) (syn_c0c)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_peano1
  have p0001 :=
    @g_tfincl (syn_c0c)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_peano1
  have p0004 :=
    @g_pw10
  have p0005 :=
    @g_peano1
  have p0006 :=
    @g_nulel0c
  have p0007 :=
    @g_tfinpw1 (syn_c0) (syn_c0c)
  have p0008 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0) (syn_c0c)) (.classMem (syn_cpw1 (syn_c0)) (syn_ctfin (syn_c0c))) p0005 p0006 p0007
  have p0009 :=
    @g_eqeltrri (syn_cpw1 (syn_c0)) (syn_c0) (syn_ctfin (syn_c0c)) p0004 p0008
  have p0010 :=
    @g_nulel0c
  have p0011 :=
    @g_nnceleq (syn_c0) (syn_ctfin (syn_c0c)) (syn_c0c)
  have p0012 :=
    @g_mp4an (.classMem (syn_ctfin (syn_c0c)) (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0) (syn_ctfin (syn_c0c))) (.classMem (syn_c0) (syn_c0c)) (.classEq (syn_ctfin (syn_c0c)) (syn_c0c)) p0002 p0003 p0009 p0010 p0011
  exact p0012

noncomputable def g_tfinsuc
    (A : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))) (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c)))) := by
  let proofSupport : Finset Var := A.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have p0000 :=
    @g_n0 a (syn_cplc A (syn_c1c)) (by exact (show a ∉ ((syn_cplc A (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((A).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))
  have p0001 :=
    @g_peano2 A
  have p0002 :=
    @g_tfincl (syn_cplc A (syn_c1c))
  have p0003 :=
    @g_syl (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_adantr (.classMem A (syn_cnnc)) (.classMem (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c))) p0003
  have p0005 :=
    @g_tfincl A
  have p0006 :=
    @g_peano2 (syn_ctfin A)
  have p0007 :=
    @g_syl (.classMem A (syn_cnnc)) (.classMem (syn_ctfin A) (syn_cnnc)) (.classMem (syn_cplc (syn_ctfin A) (syn_c1c)) (syn_cnnc)) p0005 p0006
  have p0008 :=
    @g_adantr (.classMem A (syn_cnnc)) (.classMem (syn_cplc (syn_ctfin A) (syn_c1c)) (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c))) p0007
  have p0009 :=
    @g_tfinpw1 (.cv a) (syn_cplc A (syn_c1c))
  have p0010 :=
    @g_sylan (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c))) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc A (syn_c1c)))) p0001 p0009
  have p0011 :=
    @g_elsuc x (.cv a) A b (by exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a))))))) (by exact (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a))))))) (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A))) (show b ≠ x from (by exact fresh_b_ne_x))
  have p0012 :=
    @g_tfinpw1 (.cv b) A
  have p0013 :=
    @g_adantrr (.classMem A (syn_cnnc)) (.classMem (.cv b) A) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin A)) (.classMem (.cv x) (syn_ccompl (.cv b))) p0012
  have p0014 :=
    @g_vex x
  have p0015 :=
    @g_elcompl (.cv x) (.cv b) p0014
  have p0016 :=
    @g_snelpw1 (.cv x) (.cv b)
  have p0017_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0015
  have p0017_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b))) (.objMem x b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0017 :=
    @g_xchbinxr (.classMem (.cv x) (syn_ccompl (.cv b))) (.objMem x b) (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b))) p0017_e00_recanon p0017_e01_recanon
  have p0018 :=
    @g_biimpi (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b)))) p0017
  have p0019 :=
    @g_ad2antll (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b)))) (.classMem A (syn_cnnc)) (.classMem (.cv b) A) p0018
  have p0020 :=
    @g_snex (.cv x)
  have p0021 :=
    @g_elsuci (syn_cpw1 (.cv b)) (syn_ctfin A) (syn_csn (.cv x)) p0020
  have p0022 :=
    @g_syl2anc (syn_wa (.classMem A (syn_cnnc)) (syn_wa (.classMem (.cv b) A) (.classMem (.cv x) (syn_ccompl (.cv b))))) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin A)) (.neg (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b)))) (.classMem (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x)))) (syn_cplc (syn_ctfin A) (syn_c1c))) p0013 p0019 p0021
  have p0023 :=
    @g_pw1eq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))
  have p0024 :=
    @g_pw1un (.cv b) (syn_csn (.cv x))
  have p0025 :=
    @g_pw1sn (.cv x) p0014
  have p0026 :=
    @g_uneq2i (syn_cpw1 (syn_csn (.cv x))) (syn_csn (syn_csn (.cv x))) (syn_cpw1 (.cv b)) p0025
  have p0027 :=
    @g_eqtri (syn_cpw1 (syn_cun (.cv b) (syn_csn (.cv x)))) (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (syn_csn (.cv x)))) (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x)))) p0024 p0026
  have p0028 :=
    @g_syl6eq (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cun (.cv b) (syn_csn (.cv x)))) (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x)))) p0023 p0027
  have p0029 :=
    @g_eleq1d (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (syn_cpw1 (.cv a)) (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x)))) (syn_cplc (syn_ctfin A) (syn_c1c)) p0028
  have p0030 :=
    @g_syl5ibrcom (syn_wa (.classMem A (syn_cnnc)) (syn_wa (.classMem (.cv b) A) (.classMem (.cv x) (syn_ccompl (.cv b))))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c))) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.classMem (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x)))) (syn_cplc (syn_ctfin A) (syn_c1c))) p0022 p0029
  have p0031 :=
    @g_rexlimdvva (.classMem A (syn_cnnc)) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c))) b x A (syn_ccompl (.cv b)) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_cplc (syn_ctfin A) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))))) (show b ∉ ((syn_cplc (syn_ctfin A) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((syn_ctfin A)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_ctfin A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show x ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((syn_cplc (syn_ctfin A) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a)))))))) (show x ∉ ((syn_cplc (syn_ctfin A) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((syn_ctfin A)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_ctfin A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show b ∉ ((Wff.classMem A (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((A).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (A).fv from (by exact fresh_b_not_A)) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show x ∉ ((Wff.classMem A (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show b ≠ x from (by exact fresh_b_ne_x)) p0030
  have p0032 :=
    @g_syl5bi (.classMem (.cv a) (syn_cplc A (syn_c1c))) (syn_wrex b A (syn_wrex x (syn_ccompl (.cv b)) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))))) (.classMem A (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c))) p0011 p0031
  have p0033 :=
    @g_imp (.classMem A (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c))) p0032
  have p0034 :=
    @g_nnceleq (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c))
  have p0035 :=
    @g_syl22anc (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c)))) (.classMem (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cnnc)) (.classMem (syn_cplc (syn_ctfin A) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc A (syn_c1c)))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c))) (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c))) p0004 p0008 p0010 p0033 p0034
  have p0036 :=
    @g_ex (.classMem A (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c))) (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c))) p0035
  have p0037 :=
    @g_exlimdv (.classMem A (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c))) (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c))) a (by exact (show a ∉ ((Wff.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_ctfin (syn_cplc A (syn_c1c)))).fv) ∪ (((syn_cplc (syn_ctfin A) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_ctfin (syn_cplc A (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show a ∉ ((syn_cplc A (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((A).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))) (show a ∉ ((syn_cplc (syn_ctfin A) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ (((syn_ctfin A)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_ctfin A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]; exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show a ∉ ((Wff.classMem A (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((A).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0036
  have p0038 :=
    @g_syl5bi (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) (syn_wex a (.classMem (.cv a) (syn_cplc A (syn_c1c)))) (.classMem A (syn_cnnc)) (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c))) p0000 p0037
  have p0039 :=
    @g_imp (.classMem A (syn_cnnc)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c))) p0038
  exact p0039

noncomputable def g_tfin1c
     :
    Nominal.NPrf (.classEq (syn_ctfin (syn_c1c)) (syn_c1c)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_peano1
  have p0001 :=
    @g_addcid2 (syn_c1c)
  have p0002 :=
    @g_n_1cex
  have p0003 :=
    @g_snel1c (syn_c1c) p0002
  have p0004 :=
    @g_ne0i (syn_c1c) (syn_csn (syn_c1c))
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_eqnetri (syn_cplc (syn_c0c) (syn_c1c)) (syn_c1c) (syn_c0) p0001 p0005
  have p0007 :=
    @g_tfinsuc (syn_c0c)
  have p0008 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (syn_wne (syn_cplc (syn_c0c) (syn_c1c)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (syn_c0c) (syn_c1c))) (syn_cplc (syn_ctfin (syn_c0c)) (syn_c1c))) p0000 p0006 p0007
  have p0009 :=
    @g_tfineq (syn_cplc (syn_c0c) (syn_c1c)) (syn_c1c)
  have p0010 :=
    Nominal.mp p0001 p0009
  have p0011 :=
    @g_tfin0c
  have p0012 :=
    @g_addceq1i (syn_ctfin (syn_c0c)) (syn_c0c) (syn_c1c) p0011
  have p0013 :=
    @g_eqtri (syn_cplc (syn_ctfin (syn_c0c)) (syn_c1c)) (syn_cplc (syn_c0c) (syn_c1c)) (syn_c1c) p0012 p0001
  have p0014 :=
    @g_n_3eqtr3i (syn_ctfin (syn_cplc (syn_c0c) (syn_c1c))) (syn_cplc (syn_ctfin (syn_c0c)) (syn_c1c)) (syn_ctfin (syn_c1c)) (syn_c1c) p0008 p0010 p0013
  exact p0014



#print axioms g_tfin1c

end NFChoice.DirectNominalPrf.WPPReplay
