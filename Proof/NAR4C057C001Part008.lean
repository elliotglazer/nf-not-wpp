import NAR4C057C001Part007

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

noncomputable def nb057_wpp_refl_0002 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0002 f a)

noncomputable def nb057_split_alpha_0001 (f : Var) (a : Var) (dv_a_f : a ≠ f) : TAlphaWff [((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_005)) (Class.cv (nb057_alpha_dummy_001))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_007 f a)) (Class.cv f)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0009 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0005) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0007 f a) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_a_f) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_005))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_007 f a))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0015 f a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0015 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0000 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0000 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0002 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0002 f a))))))))))))))))))))

theorem nb057_compact_fv_empty_0026 : (nb057_alpha_dummy_038) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0072 : (nb057_alpha_dummy_038) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_038, fv_syn_c1c] using (nb057_compact_fv_empty_0026)

theorem nb057_compact_fv_empty_0027 (f : Var) (a : Var) : (nb057_alpha_dummy_039 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0073 (f : Var) (a : Var) : (nb057_alpha_dummy_039 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_039, fv_syn_c1c] using (nb057_compact_fv_empty_0027 f a)

theorem nb057_compact_fv_empty_0028 : (nb057_alpha_dummy_036) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0074 : (nb057_alpha_dummy_036) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_036, fv_syn_c1c] using (nb057_compact_fv_empty_0028)

theorem nb057_compact_fv_empty_0029 (f : Var) (a : Var) : (nb057_alpha_dummy_037 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0075 (f : Var) (a : Var) : (nb057_alpha_dummy_037 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_037, fv_syn_c1c] using (nb057_compact_fv_empty_0029 f a)

theorem nb057_compact_fv_empty_0030 : (nb057_alpha_dummy_034) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0076 : (nb057_alpha_dummy_034) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_034, fv_syn_c1c] using (nb057_compact_fv_empty_0030)

theorem nb057_compact_fv_empty_0031 (f : Var) (a : Var) : (nb057_alpha_dummy_035 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0077 (f : Var) (a : Var) : (nb057_alpha_dummy_035 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_035, fv_syn_c1c] using (nb057_compact_fv_empty_0031 f a)

theorem nb057_compact_envfresh_0003 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_020) (nb057_alpha_dummy_023 f a) (nb057_wpp_notmem_0000) (nb057_wpp_notmem_0001 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_019) (nb057_alpha_dummy_022 f a) (nb057_wpp_notmem_0002) (nb057_wpp_notmem_0003 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_018) (nb057_alpha_dummy_021 f a) (nb057_wpp_notmem_0004) (nb057_wpp_notmem_0005 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_016) (nb057_alpha_dummy_017 f a) (nb057_wpp_notmem_0006) (nb057_wpp_notmem_0007 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_012) (nb057_alpha_dummy_014 f a) (nb057_wpp_notmem_0008) (nb057_wpp_notmem_0009 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_013) (nb057_alpha_dummy_015 f a) (nb057_wpp_notmem_0010) (nb057_wpp_notmem_0011 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_038) (nb057_alpha_dummy_039 f a) (nb057_wpp_notmem_0072) (nb057_wpp_notmem_0073 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_036) (nb057_alpha_dummy_037 f a) (nb057_wpp_notmem_0074) (nb057_wpp_notmem_0075 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_005) (nb057_alpha_dummy_007 f a) (nb057_wpp_notmem_0012) (nb057_wpp_notmem_0013 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_004) (nb057_alpha_dummy_006 f a) (nb057_wpp_notmem_0014) (nb057_wpp_notmem_0015 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_034) (nb057_alpha_dummy_035 f a) (nb057_wpp_notmem_0076) (nb057_wpp_notmem_0077 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_008) (nb057_alpha_dummy_009 f a) (nb057_wpp_notmem_0018) (nb057_wpp_notmem_0019 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb057_wpp_refl_0003 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0003 f a)

theorem nb057_wpp_notmem_0078 : (nb057_alpha_dummy_038) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_038, fv_syn_c0] using (nb057_compact_fv_empty_0026)

theorem nb057_wpp_notmem_0079 (f : Var) (a : Var) : (nb057_alpha_dummy_039 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_039, fv_syn_c0] using (nb057_compact_fv_empty_0027 f a)

theorem nb057_wpp_notmem_0080 : (nb057_alpha_dummy_036) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_036, fv_syn_c0] using (nb057_compact_fv_empty_0028)

theorem nb057_wpp_notmem_0081 (f : Var) (a : Var) : (nb057_alpha_dummy_037 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_037, fv_syn_c0] using (nb057_compact_fv_empty_0029 f a)

theorem nb057_wpp_notmem_0082 : (nb057_alpha_dummy_034) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_034, fv_syn_c0] using (nb057_compact_fv_empty_0030)

theorem nb057_wpp_notmem_0083 (f : Var) (a : Var) : (nb057_alpha_dummy_035 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_035, fv_syn_c0] using (nb057_compact_fv_empty_0031 f a)

theorem nb057_compact_envfresh_0004 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_020) (nb057_alpha_dummy_023 f a) (nb057_wpp_notmem_0026) (nb057_wpp_notmem_0027 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_019) (nb057_alpha_dummy_022 f a) (nb057_wpp_notmem_0028) (nb057_wpp_notmem_0029 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_018) (nb057_alpha_dummy_021 f a) (nb057_wpp_notmem_0030) (nb057_wpp_notmem_0031 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_016) (nb057_alpha_dummy_017 f a) (nb057_wpp_notmem_0032) (nb057_wpp_notmem_0033 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_012) (nb057_alpha_dummy_014 f a) (nb057_wpp_notmem_0034) (nb057_wpp_notmem_0035 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_013) (nb057_alpha_dummy_015 f a) (nb057_wpp_notmem_0036) (nb057_wpp_notmem_0037 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_038) (nb057_alpha_dummy_039 f a) (nb057_wpp_notmem_0078) (nb057_wpp_notmem_0079 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_036) (nb057_alpha_dummy_037 f a) (nb057_wpp_notmem_0080) (nb057_wpp_notmem_0081 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_005) (nb057_alpha_dummy_007 f a) (nb057_wpp_notmem_0038) (nb057_wpp_notmem_0039 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_004) (nb057_alpha_dummy_006 f a) (nb057_wpp_notmem_0040) (nb057_wpp_notmem_0041 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_034) (nb057_alpha_dummy_035 f a) (nb057_wpp_notmem_0082) (nb057_wpp_notmem_0083 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_008) (nb057_alpha_dummy_009 f a) (nb057_wpp_notmem_0044) (nb057_wpp_notmem_0045 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb057_wpp_refl_0004 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0004 f a)

noncomputable def nb057_split_alpha_0002 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_018)) (syn_cun (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_021 f a)) (syn_cun (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0019 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0017 f a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0023 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0021 f a) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0019 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0017 f a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0023 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0021 f a) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0004 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0027 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0025 f a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0027 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0025 f a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0031 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0029 f a) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0031 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0029 f a) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0084 : (nb057_alpha_dummy_038) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_038, fv_syn_cnnc] using (nb057_compact_fv_empty_0026)

theorem nb057_wpp_notmem_0085 (f : Var) (a : Var) : (nb057_alpha_dummy_039 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_039, fv_syn_cnnc] using (nb057_compact_fv_empty_0027 f a)

theorem nb057_wpp_notmem_0086 : (nb057_alpha_dummy_036) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_036, fv_syn_cnnc] using (nb057_compact_fv_empty_0028)

theorem nb057_wpp_notmem_0087 (f : Var) (a : Var) : (nb057_alpha_dummy_037 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_037, fv_syn_cnnc] using (nb057_compact_fv_empty_0029 f a)

theorem nb057_wpp_notmem_0088 : (nb057_alpha_dummy_034) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_034, fv_syn_cnnc] using (nb057_compact_fv_empty_0030)

theorem nb057_wpp_notmem_0089 (f : Var) (a : Var) : (nb057_alpha_dummy_035 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_035, fv_syn_cnnc] using (nb057_compact_fv_empty_0031 f a)

theorem nb057_compact_envfresh_0005 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_016) (nb057_alpha_dummy_017 f a) (nb057_wpp_notmem_0052) (nb057_wpp_notmem_0053 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_012) (nb057_alpha_dummy_014 f a) (nb057_wpp_notmem_0054) (nb057_wpp_notmem_0055 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_013) (nb057_alpha_dummy_015 f a) (nb057_wpp_notmem_0056) (nb057_wpp_notmem_0057 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_038) (nb057_alpha_dummy_039 f a) (nb057_wpp_notmem_0084) (nb057_wpp_notmem_0085 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_036) (nb057_alpha_dummy_037 f a) (nb057_wpp_notmem_0086) (nb057_wpp_notmem_0087 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_005) (nb057_alpha_dummy_007 f a) (nb057_wpp_notmem_0058) (nb057_wpp_notmem_0059 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_004) (nb057_alpha_dummy_006 f a) (nb057_wpp_notmem_0060) (nb057_wpp_notmem_0061 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_034) (nb057_alpha_dummy_035 f a) (nb057_wpp_notmem_0088) (nb057_wpp_notmem_0089 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_008) (nb057_alpha_dummy_009 f a) (nb057_wpp_notmem_0064) (nb057_wpp_notmem_0065 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb057_wpp_refl_0005 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0005 f a)

noncomputable def nb057_split_alpha_0003 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_038)) (syn_cphi (Class.cv (nb057_alpha_dummy_005)))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_038)) (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_039 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_039 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0041 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0039 f a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_005))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_007 f a))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0015 f a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0015 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0003 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0002 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0005 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0005 f a)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0041 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0039 f a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_005))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_007 f a))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0015 f a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0015 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0003 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0002 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0005 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0005 f a))))))))))))))))))))

theorem nb057_wpp_notmem_0090 : (nb057_alpha_dummy_036) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_036, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0028)

theorem nb057_wpp_notmem_0091 (f : Var) (a : Var) : (nb057_alpha_dummy_037 f a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0029 f a)

theorem nb057_wpp_notmem_0092 : (nb057_alpha_dummy_005) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0012)

theorem nb057_wpp_notmem_0093 (f : Var) (a : Var) : (nb057_alpha_dummy_007 f a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0013 f a)

theorem nb057_wpp_notmem_0094 : (nb057_alpha_dummy_004) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0014)

theorem nb057_wpp_notmem_0095 (f : Var) (a : Var) : (nb057_alpha_dummy_006 f a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0015 f a)

theorem nb057_wpp_notmem_0096 : (nb057_alpha_dummy_034) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_034, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0030)

theorem nb057_wpp_notmem_0097 (f : Var) (a : Var) : (nb057_alpha_dummy_035 f a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0031 f a)

theorem nb057_wpp_notmem_0098 : (nb057_alpha_dummy_008) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0018)

theorem nb057_wpp_notmem_0099 (f : Var) (a : Var) : (nb057_alpha_dummy_009 f a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0019 f a)

theorem nb057_wpp_notmem_0100 : (nb057_alpha_dummy_000) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0020)

theorem nb057_wpp_notmem_0101 (a : Var) : a ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0021 a)

theorem nb057_wpp_notmem_0102 : (nb057_alpha_dummy_001) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0022)

theorem nb057_wpp_notmem_0103 (f : Var) : f ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0023 f)

theorem nb057_wpp_notmem_0104 : (nb057_alpha_dummy_002) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0024)

theorem nb057_wpp_notmem_0105 (f : Var) (a : Var) : (nb057_alpha_dummy_003 f a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0025 f a)

theorem nb057_compact_envfresh_0006 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_036) (nb057_alpha_dummy_037 f a) (nb057_wpp_notmem_0090) (nb057_wpp_notmem_0091 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_005) (nb057_alpha_dummy_007 f a) (nb057_wpp_notmem_0092) (nb057_wpp_notmem_0093 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_004) (nb057_alpha_dummy_006 f a) (nb057_wpp_notmem_0094) (nb057_wpp_notmem_0095 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_034) (nb057_alpha_dummy_035 f a) (nb057_wpp_notmem_0096) (nb057_wpp_notmem_0097 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_008) (nb057_alpha_dummy_009 f a) (nb057_wpp_notmem_0098) (nb057_wpp_notmem_0099 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0100) (nb057_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0102) (nb057_wpp_notmem_0103 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0104) (nb057_wpp_notmem_0105 f a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb057_wpp_refl_0006 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0006 f a)

noncomputable def nb057_split_alpha_0004 (f : Var) (a : Var) (dv_a_f : a ≠ f) : TAlphaWff [((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.classEq (Class.cv (nb057_alpha_dummy_002)) (syn_cop (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))) (Wff.classEq (Class.cv (nb057_alpha_dummy_003 f a)) (syn_cop (Class.cv f) (Class.cv a))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0002) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0003 f a) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0000) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0001 f a) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0001 f a dv_a_f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0001 f a dv_a_f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0037 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0035 f a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0003 f a))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0006 f a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0037 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0035 f a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0003 f a))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0006 f a)))))))))))))))))))))))))))))

theorem nb057_compact_fv_empty_0032 : (nb057_alpha_dummy_068) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0106 : (nb057_alpha_dummy_068) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_068, fv_syn_c1c] using (nb057_compact_fv_empty_0032)

theorem nb057_compact_fv_empty_0033 (f : Var) : (nb057_alpha_dummy_071 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0107 (f : Var) : (nb057_alpha_dummy_071 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_071, fv_syn_c1c] using (nb057_compact_fv_empty_0033 f)

theorem nb057_compact_fv_empty_0034 : (nb057_alpha_dummy_067) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0108 : (nb057_alpha_dummy_067) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_067, fv_syn_c1c] using (nb057_compact_fv_empty_0034)

theorem nb057_compact_fv_empty_0035 (f : Var) : (nb057_alpha_dummy_070 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0109 (f : Var) : (nb057_alpha_dummy_070 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_070, fv_syn_c1c] using (nb057_compact_fv_empty_0035 f)

theorem nb057_compact_fv_empty_0036 : (nb057_alpha_dummy_066) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0110 : (nb057_alpha_dummy_066) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_066, fv_syn_c1c] using (nb057_compact_fv_empty_0036)

theorem nb057_compact_fv_empty_0037 (f : Var) : (nb057_alpha_dummy_069 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0111 (f : Var) : (nb057_alpha_dummy_069 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_069, fv_syn_c1c] using (nb057_compact_fv_empty_0037 f)

theorem nb057_compact_fv_empty_0038 : (nb057_alpha_dummy_064) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0112 : (nb057_alpha_dummy_064) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_064, fv_syn_c1c] using (nb057_compact_fv_empty_0038)

theorem nb057_compact_fv_empty_0039 (f : Var) : (nb057_alpha_dummy_065 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0113 (f : Var) : (nb057_alpha_dummy_065 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_065, fv_syn_c1c] using (nb057_compact_fv_empty_0039 f)

theorem nb057_compact_fv_empty_0040 : (nb057_alpha_dummy_060) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0114 : (nb057_alpha_dummy_060) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_060, fv_syn_c1c] using (nb057_compact_fv_empty_0040)

theorem nb057_compact_fv_empty_0041 (f : Var) : (nb057_alpha_dummy_062 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0115 (f : Var) : (nb057_alpha_dummy_062 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_062, fv_syn_c1c] using (nb057_compact_fv_empty_0041 f)

theorem nb057_compact_fv_empty_0042 : (nb057_alpha_dummy_061) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0116 : (nb057_alpha_dummy_061) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_061, fv_syn_c1c] using (nb057_compact_fv_empty_0042)

theorem nb057_compact_fv_empty_0043 (f : Var) : (nb057_alpha_dummy_063 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0117 (f : Var) : (nb057_alpha_dummy_063 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_063, fv_syn_c1c] using (nb057_compact_fv_empty_0043 f)

theorem nb057_compact_fv_empty_0044 : (nb057_alpha_dummy_053) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0118 : (nb057_alpha_dummy_053) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_053, fv_syn_c1c] using (nb057_compact_fv_empty_0044)

theorem nb057_compact_fv_empty_0045 (f : Var) : (nb057_alpha_dummy_055 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0119 (f : Var) : (nb057_alpha_dummy_055 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_055, fv_syn_c1c] using (nb057_compact_fv_empty_0045 f)

theorem nb057_compact_fv_empty_0046 : (nb057_alpha_dummy_052) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0120 : (nb057_alpha_dummy_052) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_052, fv_syn_c1c] using (nb057_compact_fv_empty_0046)

theorem nb057_compact_fv_empty_0047 (f : Var) : (nb057_alpha_dummy_054 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0121 (f : Var) : (nb057_alpha_dummy_054 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_054, fv_syn_c1c] using (nb057_compact_fv_empty_0047 f)

theorem nb057_compact_fv_empty_0048 : (nb057_alpha_dummy_058) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0122 : (nb057_alpha_dummy_058) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_058, fv_syn_c1c] using (nb057_compact_fv_empty_0048)

theorem nb057_compact_fv_empty_0049 (f : Var) : (nb057_alpha_dummy_059 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0123 (f : Var) : (nb057_alpha_dummy_059 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_059, fv_syn_c1c] using (nb057_compact_fv_empty_0049 f)

theorem nb057_compact_fv_empty_0050 : (nb057_alpha_dummy_056) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0124 : (nb057_alpha_dummy_056) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_056, fv_syn_c1c] using (nb057_compact_fv_empty_0050)

theorem nb057_compact_fv_empty_0051 (f : Var) : (nb057_alpha_dummy_057 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0125 (f : Var) : (nb057_alpha_dummy_057 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_057, fv_syn_c1c] using (nb057_compact_fv_empty_0051 f)

theorem nb057_compact_fv_empty_0052 : (nb057_alpha_dummy_045) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0126 : (nb057_alpha_dummy_045) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_045, fv_syn_c1c] using (nb057_compact_fv_empty_0052)

theorem nb057_compact_fv_empty_0053 (f : Var) : (nb057_alpha_dummy_048 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0127 (f : Var) : (nb057_alpha_dummy_048 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_048, fv_syn_c1c] using (nb057_compact_fv_empty_0053 f)

theorem nb057_compact_fv_empty_0054 : (nb057_alpha_dummy_044) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0128 : (nb057_alpha_dummy_044) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_044, fv_syn_c1c] using (nb057_compact_fv_empty_0054)

theorem nb057_compact_fv_empty_0055 (f : Var) : (nb057_alpha_dummy_047 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0129 (f : Var) : (nb057_alpha_dummy_047 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_047, fv_syn_c1c] using (nb057_compact_fv_empty_0055 f)

theorem nb057_compact_fv_empty_0056 : (nb057_alpha_dummy_050) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0130 : (nb057_alpha_dummy_050) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_050, fv_syn_c1c] using (nb057_compact_fv_empty_0056)

theorem nb057_compact_fv_empty_0057 (f : Var) : (nb057_alpha_dummy_051 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0131 (f : Var) : (nb057_alpha_dummy_051 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_051, fv_syn_c1c] using (nb057_compact_fv_empty_0057 f)

theorem nb057_compact_fv_empty_0058 : (nb057_alpha_dummy_042) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0132 : (nb057_alpha_dummy_042) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_042, fv_syn_c1c] using (nb057_compact_fv_empty_0058)

theorem nb057_compact_fv_empty_0059 (f : Var) : (nb057_alpha_dummy_043 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0133 (f : Var) : (nb057_alpha_dummy_043 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_043, fv_syn_c1c] using (nb057_compact_fv_empty_0059 f)

theorem nb057_compact_fv_empty_0060 : (nb057_alpha_dummy_040) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0134 : (nb057_alpha_dummy_040) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_040, fv_syn_c1c] using (nb057_compact_fv_empty_0060)

theorem nb057_compact_fv_empty_0061 (f : Var) : (nb057_alpha_dummy_041 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0135 (f : Var) : (nb057_alpha_dummy_041 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_041, fv_syn_c1c] using (nb057_compact_fv_empty_0061 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
