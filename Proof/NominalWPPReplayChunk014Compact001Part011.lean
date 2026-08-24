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
import NominalWPPReplayChunk014Compact001Part010

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

noncomputable def g_fdsepvalJ
    (A : Class) (B : Class) (C : Class) (D : Class) (e : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_e : e ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_e : e ∉ C.fv) (dv_D_e : e ∉ D.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem C B) (.classMem D B)) (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ ({e} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_e : z ≠ e := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_e_ne_z : e ≠ z :=
    Ne.symm fresh_z_ne_e
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : e ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0007 : e ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0009 : e ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : e ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv e)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, fresh_z_ne_e, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cfdsep] using (Nominal.classEqRefl (syn_cfdsep A B)))
  have p0001 :=
    @g_eleq2i (syn_cfdsep A B) (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B)) (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0000
  have p0002 :=
    @g_elsymdif (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B) (syn_cfde1 A B)
  have p0003 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B))) (.neg (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B)))) p0001 p0002
  have p0004 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))))) (syn_wa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @g_fde0valJp A B C D e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0006 :=
    @g_fde1valJp A B C D e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0007 :=
    @g_bibi12d (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B)) (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))) p0005 p0006
  have p0008 :=
    @g_notbid (syn_wa (.classMem C B) (.classMem D B)) (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))) (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))) (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e)))) p0007
  have p0009 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B)))) (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))) (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))))) p0004 p0008
  have p0010 :=
    @g_xordi (.classMem (.cv e) A) (.classMem C (.cv e)) (.classMem D (.cv e))
  have p0011 :=
    @g_bicomi (syn_wa (.classMem (.cv e) A) (.neg (syn_wb (.classMem C (.cv e)) (.classMem D (.cv e))))) (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))) (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))))) p0010
  have p0012 :=
    @g_xor (.classMem C (.cv e)) (.classMem D (.cv e))
  have p0013 :=
    @g_anbi2i (.neg (syn_wb (.classMem C (.cv e)) (.classMem D (.cv e)))) (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))) (.classMem (.cv e) A) p0012
  have p0014 :=
    @g_bitri (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))) (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))))) (syn_wa (.classMem (.cv e) A) (.neg (syn_wb (.classMem C (.cv e)) (.classMem D (.cv e))))) (syn_wa (.classMem (.cv e) A) (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))) p0011 p0013
  have p0015 :=
    @g_a1i (syn_wb (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))) (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))))) (syn_wa (.classMem (.cv e) A) (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))))) (syn_wa (.classMem C B) (.classMem D B)) p0014
  have p0016 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))) (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))))) (syn_wa (.classMem (.cv e) A) (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))) p0009 p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sep2 z C D dv_cache_0008 dv_cache_0011 dv_cache_0012
  have p0018 :=
    @g_eleq2i (syn_csep2 C D) (.cab z (syn_wo (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z)))) (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))))) (.cv e) p0017
  have p0019 :=
    @g_vex e
  have p0020 :=
    @g_eleq2 (.cv z) (.cv e) C
  have p0021 :=
    @g_eleq2 (.cv z) (.cv e) D
  have p0022 :=
    @g_notbid (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e)) p0021
  have p0023 :=
    @g_anbi12d (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e)) (.neg (.classMem D (.cv z))) (.neg (.classMem D (.cv e))) p0020 p0022
  have p0024 :=
    @g_eleq2 (.cv z) (.cv e) D
  have p0025 :=
    @g_eleq2 (.cv z) (.cv e) C
  have p0026 :=
    @g_notbid (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e)) p0025
  have p0027 :=
    @g_anbi12d (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e)) (.neg (.classMem C (.cv z))) (.neg (.classMem C (.cv e))) p0024 p0026
  have p0028 :=
    @g_orbi12d (.classEq (.cv z) (.cv e)) (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z)))) (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))) p0023 p0027
  have p0029 :=
    @g_elab (syn_wo (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z)))) (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))) (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))) z (.cv e) dv_cache_0013 dv_cache_0014 p0019 p0028
  have p0030 :=
    @g_bitri (.classMem (.cv e) (syn_csep2 C D)) (.classMem (.cv e) (.cab z (syn_wo (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z)))) (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))))) (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))) p0018 p0029
  have p0031 :=
    @g_bicomi (.classMem (.cv e) (syn_csep2 C D)) (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))) p0030
  have p0032 :=
    @g_anbi2i (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))) (.classMem (.cv e) (syn_csep2 C D)) (.classMem (.cv e) A) p0031
  have p0033 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv e) A) (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))) (syn_wa (.classMem C B) (.classMem D B)) p0032
  have p0034 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (syn_wa (.classMem (.cv e) A) (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e)))) (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) p0016 p0033
  exact p0034

noncomputable def g_strictbr
    (R : Class) (e : Var) (c : Var) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e)))) := by
  let proofSupport : Finset Var := R.fv ∪ ({e} : Finset Var) ∪ ({c} : Finset Var)
  have p0000 :=
    @g_brdif (.cv c) (.cv e) R (syn_cid)
  have p0001 :=
    @g_vex e
  have p0002 :=
    @g_ideq (.cv c) (.cv e) p0001
  have p0003 :=
    @g_notbii (syn_wbr (.cv c) (syn_cid) (.cv e)) (.classEq (.cv c) (.cv e)) p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv c) (.cv e))))
  have p0005 :=
    @g_bicomi (syn_wne (.cv c) (.cv e)) (.neg (.classEq (.cv c) (.cv e))) p0004
  have p0006 :=
    @g_bitri (.neg (syn_wbr (.cv c) (syn_cid) (.cv e))) (.neg (.classEq (.cv c) (.cv e))) (syn_wne (.cv c) (.cv e)) p0003 p0005
  have p0007 :=
    @g_anbi2i (.neg (syn_wbr (.cv c) (syn_cid) (.cv e))) (syn_wne (.cv c) (.cv e)) (syn_wbr (.cv c) R (.cv e)) p0006
  have p0008 :=
    @g_bitri (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wa (syn_wbr (.cv c) R (.cv e)) (.neg (syn_wbr (.cv c) (syn_cid) (.cv e)))) (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) p0000 p0007
  exact p0008

noncomputable def g_fdnonminval0J
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (e : Var) (c : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (dv_A_e : e ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_c : c ∉ B.fv) (dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_c : c ∉ C.fv) (dv_C_e : e ∉ C.fv) (dv_D_R : Disjoint D.fv R.fv) (dv_D_c : c ∉ D.fv) (dv_D_e : e ∉ D.fv) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf (.imp (syn_wa (.classMem C B) (.classMem D B)) (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({e} : Finset Var) ∪ ({c} : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_e : x ≠ e := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_e_ne_x : e ≠ x :=
    Ne.symm fresh_x_ne_e
  have fresh_x_ne_c : x ≠ c := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_x : c ≠ x :=
    Ne.symm fresh_x_ne_c
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : c ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0007 : c ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0009 : c ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : c ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : c ∉ ((syn_wa (.classMem C B) (.classMem D B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_c, dv_B_c, dv_D_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_csn (.cv e))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_cfdsep A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdlift, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : c ∉ ((syn_cdif R (syn_cid))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : e ∉ ((syn_cdif R (syn_cid))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_cdif R (syn_cid))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : c ≠ e := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show c ≠ e from (by exact dv_c_e))
  have dv_cache_0020 : c ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show c ≠ x from (by exact fresh_c_ne_x))
  have dv_cache_0021 : e ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show e ≠ x from (by exact fresh_e_ne_x))
  have dv_cache_0022 : c ∉ ((Wff.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, dv_C_c, dv_D_c, dv_A_c, dv_B_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_csn (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_e, fresh_x_not_R, fresh_x_not_C, fresh_x_not_D, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdsepvalJ A B C D c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_anbi2d (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)) (syn_wa (.classMem (.cv c) A) (.classMem (.cv c) (syn_csep2 C D))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0000
  have p0002 :=
    @g_an12 (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) A) (.classMem (.cv c) (syn_csep2 C D))
  have p0003 :=
    @g_a1i (syn_wb (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wa (.classMem (.cv c) A) (.classMem (.cv c) (syn_csep2 C D)))) (syn_wa (.classMem (.cv c) A) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))) (syn_wa (.classMem C B) (.classMem D B)) p0002
  have p0004 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B))) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wa (.classMem (.cv c) A) (.classMem (.cv c) (syn_csep2 C D)))) (syn_wa (.classMem (.cv c) A) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))) p0001 p0003
  have p0005 :=
    @g_exbidv (syn_wa (.classMem C B) (.classMem D B)) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B))) (syn_wa (.classMem (.cv c) A) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))) c dv_cache_0011 p0004
  have p0006 :=
    (by simpa [syn_cfdnonmin] using (Nominal.classEqRefl (syn_cfdnonmin R A B)))
  have p0007 :=
    @g_eleq2i (syn_cfdnonmin R A B) (syn_ccomk (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid))))) (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0006
  have p0008 :=
    @g_snex (.cv e)
  have p0009 :=
    @g_opkex C D
  have p0010 :=
    @g_opkelcok x (syn_csn (.cv e)) (syn_copk C D) (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0008 p0009
  have p0011 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))))) (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid))))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) p0007 p0010
  have p0012 :=
    @g_snex (.cv e)
  have p0013 :=
    @g_vex x
  have p0014 :=
    @g_opkelcnvk (syn_csn (.cv e)) (.cv x) (syn_cfdlift (syn_cdif R (syn_cid))) p0012 p0013
  have p0015 :=
    @g_biid (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))
  have p0016 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid))))) (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift (syn_cdif R (syn_cid)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)) p0014 p0015
  have p0017 :=
    @g_exbii (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid))))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))) (syn_wa (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift (syn_cdif R (syn_cid)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))) x p0016
  have p0018 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid))))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) (syn_wex x (syn_wa (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift (syn_cdif R (syn_cid)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) p0011 p0017
  have p0019 :=
    @g_fdliftval1 x (syn_cdif R (syn_cid)) e c dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0020 :=
    @g_biid (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))
  have p0021 :=
    @g_anbi12i (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift (syn_cdif R (syn_cid)))) (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)) p0019 p0020
  have p0022 :=
    @g_exbii (syn_wa (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift (syn_cdif R (syn_cid)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))) (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))) x p0021
  have p0023 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (syn_wex x (syn_wa (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift (syn_cdif R (syn_cid)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) (syn_wex x (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) p0018 p0022
  have p0024 :=
    @g_n_19_41v (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)) c dv_cache_0022
  have p0025 :=
    @g_bicomi (syn_wex c (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))) p0024
  have p0026 :=
    @g_exbii (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))) (syn_wex c (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) x p0025
  have p0027 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (syn_wex x (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) (syn_wex x (syn_wex c (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))) p0023 p0026
  have p0028 :=
    @g_excom (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))) x c
  have p0029 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (syn_wex x (syn_wex c (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))) (syn_wex c (syn_wex x (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))) p0027 p0028
  have p0030 :=
    @g_anass (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))
  have p0031 :=
    @g_exbii (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))) (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) x p0030
  have p0032 :=
    @g_exbii (syn_wex x (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))) c p0031
  have p0033 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (syn_wex c (syn_wex x (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))) (syn_wex c (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))))) p0029 p0032
  have p0034 :=
    @g_snex (.cv c)
  have p0035 :=
    @g_opkeq1 (.cv x) (syn_csn (.cv c)) (syn_copk C D)
  have p0036 :=
    @g_eleq1d (.classEq (.cv x) (syn_csn (.cv c))) (syn_copk (.cv x) (syn_copk C D)) (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B) p0035
  have p0037 :=
    @g_anbi2d (.classEq (.cv x) (syn_csn (.cv c))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0036
  have p0038 :=
    @g_ceqsexv (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B))) x (syn_csn (.cv c)) dv_cache_0023 dv_cache_0024 p0034 p0037
  have p0039 :=
    @g_exbii (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B))) c p0038
  have p0040 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (syn_wex c (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))))) (syn_wex c (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)))) p0033 p0039
  have p0041 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))))
  have p0042 :=
    @g_n_3bitr4g (syn_wa (.classMem C B) (.classMem D B)) (syn_wex c (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)))) (syn_wex c (syn_wa (.classMem (.cv c) A) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))) p0005 p0040 p0041
  exact p0042

noncomputable def g_kqrelex
    (A : Class) (hyp_kqrelex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ckqrel A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_kqrel x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_setconslem4 x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_eqtr4i (syn_ckqrel A) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A)) (syn_cuni1 (syn_cuni1 (syn_cimak (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) A))) p0000 p0001
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_vvex
  have p0005 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0003 p0004
  have p0006 :=
    @g_vvex
  have p0007 :=
    @g_xpkex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv) p0005 p0006
  have p0008 :=
    @g_setconslem5
  have p0009 :=
    @g_cnvkex (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0008
  have p0010 :=
    @g_inex (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0007 p0009
  have p0011 :=
    @g_imakex (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) A p0010 hyp_kqrelex_1
  have p0012 :=
    @g_uni1ex (syn_cimak (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) A) p0011
  have p0013 :=
    @g_uni1ex (syn_cuni1 (syn_cimak (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) A)) p0012
  have p0014 :=
    @g_eqeltri (syn_ckqrel A) (syn_cuni1 (syn_cuni1 (syn_cimak (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) A))) (syn_cvv) p0002 p0013
  exact p0014

#print axioms g_kqrelex

end NFChoice.DirectNominalPrf.WPPReplay
