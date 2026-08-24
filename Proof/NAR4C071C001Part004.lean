import NAR4C071C001Part003

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

theorem nb071_wpp_notmem_0063 (x : Var) : (nb071_alpha_dummy_012 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_012, fv_syn_cnnc] using (nb071_compact_fv_empty_0017 x)

theorem nb071_wpp_notmem_0064 : (nb071_alpha_dummy_009) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_009, fv_syn_cnnc] using (nb071_compact_fv_empty_0018)

theorem nb071_wpp_notmem_0065 (x : Var) : (nb071_alpha_dummy_010 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_010, fv_syn_cnnc] using (nb071_compact_fv_empty_0019 x)

theorem nb071_wpp_notmem_0066 : (nb071_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_001, fv_syn_cnnc] using (nb071_compact_fv_empty_0020)

theorem nb071_wpp_notmem_0067 (x : Var) : (nb071_alpha_dummy_002 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_002, fv_syn_cnnc] using (nb071_compact_fv_empty_0021 x)

theorem nb071_wpp_notmem_0068 : (nb071_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_000, fv_syn_cnnc] using (nb071_compact_fv_empty_0022)

theorem nb071_wpp_notmem_0069 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb071_compact_fv_empty_0023 x)

theorem nb071_wpp_notmem_0070 : (nb071_alpha_dummy_003) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_003, fv_syn_cnnc] using (nb071_compact_fv_empty_0024)

theorem nb071_wpp_notmem_0071 (x : Var) : (nb071_alpha_dummy_004 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_004, fv_syn_cnnc] using (nb071_compact_fv_empty_0025 x)

theorem nb071_compact_envfresh_0002 (x : Var) : TEnvFresh [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_017) (nb071_alpha_dummy_018 x) (nb071_wpp_notmem_0052) (nb071_wpp_notmem_0053 x) (TEnvFresh.consFresh (nb071_alpha_dummy_013) (nb071_alpha_dummy_015 x) (nb071_wpp_notmem_0054) (nb071_wpp_notmem_0055 x) (TEnvFresh.consFresh (nb071_alpha_dummy_014) (nb071_alpha_dummy_016 x) (nb071_wpp_notmem_0056) (nb071_wpp_notmem_0057 x) (TEnvFresh.consFresh (nb071_alpha_dummy_006) (nb071_alpha_dummy_008 x) (nb071_wpp_notmem_0058) (nb071_wpp_notmem_0059 x) (TEnvFresh.consFresh (nb071_alpha_dummy_005) (nb071_alpha_dummy_007 x) (nb071_wpp_notmem_0060) (nb071_wpp_notmem_0061 x) (TEnvFresh.consFresh (nb071_alpha_dummy_011) (nb071_alpha_dummy_012 x) (nb071_wpp_notmem_0062) (nb071_wpp_notmem_0063 x) (TEnvFresh.consFresh (nb071_alpha_dummy_009) (nb071_alpha_dummy_010 x) (nb071_wpp_notmem_0064) (nb071_wpp_notmem_0065 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0066) (nb071_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0068) (nb071_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0070) (nb071_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb071_wpp_refl_0002 (x : Var) : TReflOn [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0002 x)

noncomputable def nb071_split_alpha_0001 (x : Var) : TAlphaWff [((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_006)) (Class.cv (nb071_alpha_dummy_000))) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_005)) (syn_cphi (Class.cv (nb071_alpha_dummy_006)))))) (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_008 x)) (Class.cv x)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0011 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0007) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0009 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0013 x) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0016) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0017 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_c1c) (nb071_wpp_refl_0000 x))) (TAlphaWff.neg (TAlphaWff.neg (nb071_split_alpha_0000 x)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_cnnc) (nb071_wpp_refl_0002 x))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_cnnc) (nb071_wpp_refl_0002 x))))))))))))))))))))

theorem nb071_compact_fv_empty_0026 : (nb071_alpha_dummy_039) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0072 : (nb071_alpha_dummy_039) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_039, fv_syn_c1c] using (nb071_compact_fv_empty_0026)

theorem nb071_compact_fv_empty_0027 (x : Var) : (nb071_alpha_dummy_040 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0073 (x : Var) : (nb071_alpha_dummy_040 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_040, fv_syn_c1c] using (nb071_compact_fv_empty_0027 x)

theorem nb071_compact_fv_empty_0028 : (nb071_alpha_dummy_037) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0074 : (nb071_alpha_dummy_037) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_037, fv_syn_c1c] using (nb071_compact_fv_empty_0028)

theorem nb071_compact_fv_empty_0029 (x : Var) : (nb071_alpha_dummy_038 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0075 (x : Var) : (nb071_alpha_dummy_038 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_038, fv_syn_c1c] using (nb071_compact_fv_empty_0029 x)

theorem nb071_compact_fv_empty_0030 : (nb071_alpha_dummy_035) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0076 : (nb071_alpha_dummy_035) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_035, fv_syn_c1c] using (nb071_compact_fv_empty_0030)

theorem nb071_compact_fv_empty_0031 (x : Var) : (nb071_alpha_dummy_036 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0077 (x : Var) : (nb071_alpha_dummy_036 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_036, fv_syn_c1c] using (nb071_compact_fv_empty_0031 x)

theorem nb071_compact_envfresh_0003 (x : Var) : TEnvFresh [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_021) (nb071_alpha_dummy_024 x) (nb071_wpp_notmem_0000) (nb071_wpp_notmem_0001 x) (TEnvFresh.consFresh (nb071_alpha_dummy_020) (nb071_alpha_dummy_023 x) (nb071_wpp_notmem_0002) (nb071_wpp_notmem_0003 x) (TEnvFresh.consFresh (nb071_alpha_dummy_019) (nb071_alpha_dummy_022 x) (nb071_wpp_notmem_0004) (nb071_wpp_notmem_0005 x) (TEnvFresh.consFresh (nb071_alpha_dummy_017) (nb071_alpha_dummy_018 x) (nb071_wpp_notmem_0006) (nb071_wpp_notmem_0007 x) (TEnvFresh.consFresh (nb071_alpha_dummy_013) (nb071_alpha_dummy_015 x) (nb071_wpp_notmem_0008) (nb071_wpp_notmem_0009 x) (TEnvFresh.consFresh (nb071_alpha_dummy_014) (nb071_alpha_dummy_016 x) (nb071_wpp_notmem_0010) (nb071_wpp_notmem_0011 x) (TEnvFresh.consFresh (nb071_alpha_dummy_039) (nb071_alpha_dummy_040 x) (nb071_wpp_notmem_0072) (nb071_wpp_notmem_0073 x) (TEnvFresh.consFresh (nb071_alpha_dummy_037) (nb071_alpha_dummy_038 x) (nb071_wpp_notmem_0074) (nb071_wpp_notmem_0075 x) (TEnvFresh.consFresh (nb071_alpha_dummy_006) (nb071_alpha_dummy_008 x) (nb071_wpp_notmem_0012) (nb071_wpp_notmem_0013 x) (TEnvFresh.consFresh (nb071_alpha_dummy_005) (nb071_alpha_dummy_007 x) (nb071_wpp_notmem_0014) (nb071_wpp_notmem_0015 x) (TEnvFresh.consFresh (nb071_alpha_dummy_035) (nb071_alpha_dummy_036 x) (nb071_wpp_notmem_0076) (nb071_wpp_notmem_0077 x) (TEnvFresh.consFresh (nb071_alpha_dummy_009) (nb071_alpha_dummy_010 x) (nb071_wpp_notmem_0018) (nb071_wpp_notmem_0019 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0020) (nb071_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0022) (nb071_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0024) (nb071_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb071_wpp_refl_0003 (x : Var) : TReflOn [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0003 x)

theorem nb071_wpp_notmem_0078 : (nb071_alpha_dummy_039) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_039, fv_syn_c0] using (nb071_compact_fv_empty_0026)

theorem nb071_wpp_notmem_0079 (x : Var) : (nb071_alpha_dummy_040 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_040, fv_syn_c0] using (nb071_compact_fv_empty_0027 x)

theorem nb071_wpp_notmem_0080 : (nb071_alpha_dummy_037) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_037, fv_syn_c0] using (nb071_compact_fv_empty_0028)

theorem nb071_wpp_notmem_0081 (x : Var) : (nb071_alpha_dummy_038 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_038, fv_syn_c0] using (nb071_compact_fv_empty_0029 x)

theorem nb071_wpp_notmem_0082 : (nb071_alpha_dummy_035) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_035, fv_syn_c0] using (nb071_compact_fv_empty_0030)

theorem nb071_wpp_notmem_0083 (x : Var) : (nb071_alpha_dummy_036 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_036, fv_syn_c0] using (nb071_compact_fv_empty_0031 x)

theorem nb071_compact_envfresh_0004 (x : Var) : TEnvFresh [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_021) (nb071_alpha_dummy_024 x) (nb071_wpp_notmem_0026) (nb071_wpp_notmem_0027 x) (TEnvFresh.consFresh (nb071_alpha_dummy_020) (nb071_alpha_dummy_023 x) (nb071_wpp_notmem_0028) (nb071_wpp_notmem_0029 x) (TEnvFresh.consFresh (nb071_alpha_dummy_019) (nb071_alpha_dummy_022 x) (nb071_wpp_notmem_0030) (nb071_wpp_notmem_0031 x) (TEnvFresh.consFresh (nb071_alpha_dummy_017) (nb071_alpha_dummy_018 x) (nb071_wpp_notmem_0032) (nb071_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb071_alpha_dummy_013) (nb071_alpha_dummy_015 x) (nb071_wpp_notmem_0034) (nb071_wpp_notmem_0035 x) (TEnvFresh.consFresh (nb071_alpha_dummy_014) (nb071_alpha_dummy_016 x) (nb071_wpp_notmem_0036) (nb071_wpp_notmem_0037 x) (TEnvFresh.consFresh (nb071_alpha_dummy_039) (nb071_alpha_dummy_040 x) (nb071_wpp_notmem_0078) (nb071_wpp_notmem_0079 x) (TEnvFresh.consFresh (nb071_alpha_dummy_037) (nb071_alpha_dummy_038 x) (nb071_wpp_notmem_0080) (nb071_wpp_notmem_0081 x) (TEnvFresh.consFresh (nb071_alpha_dummy_006) (nb071_alpha_dummy_008 x) (nb071_wpp_notmem_0038) (nb071_wpp_notmem_0039 x) (TEnvFresh.consFresh (nb071_alpha_dummy_005) (nb071_alpha_dummy_007 x) (nb071_wpp_notmem_0040) (nb071_wpp_notmem_0041 x) (TEnvFresh.consFresh (nb071_alpha_dummy_035) (nb071_alpha_dummy_036 x) (nb071_wpp_notmem_0082) (nb071_wpp_notmem_0083 x) (TEnvFresh.consFresh (nb071_alpha_dummy_009) (nb071_alpha_dummy_010 x) (nb071_wpp_notmem_0044) (nb071_wpp_notmem_0045 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0046) (nb071_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0048) (nb071_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0050) (nb071_wpp_notmem_0051 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb071_wpp_refl_0004 (x : Var) : TReflOn [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0004 x)

noncomputable def nb071_split_alpha_0002 (x : Var) : TAlphaWff [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_019)) (syn_cun (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_023 x)) (Class.cv (nb071_alpha_dummy_024 x))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_022 x)) (syn_cun (Class.cv (nb071_alpha_dummy_023 x)) (Class.cv (nb071_alpha_dummy_024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_c0) (nb071_wpp_refl_0004 x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb071_wpp_notmem_0084 : (nb071_alpha_dummy_039) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_039, fv_syn_cnnc] using (nb071_compact_fv_empty_0026)

theorem nb071_wpp_notmem_0085 (x : Var) : (nb071_alpha_dummy_040 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_040, fv_syn_cnnc] using (nb071_compact_fv_empty_0027 x)

theorem nb071_wpp_notmem_0086 : (nb071_alpha_dummy_037) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_037, fv_syn_cnnc] using (nb071_compact_fv_empty_0028)

theorem nb071_wpp_notmem_0087 (x : Var) : (nb071_alpha_dummy_038 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_038, fv_syn_cnnc] using (nb071_compact_fv_empty_0029 x)

theorem nb071_wpp_notmem_0088 : (nb071_alpha_dummy_035) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_035, fv_syn_cnnc] using (nb071_compact_fv_empty_0030)

theorem nb071_wpp_notmem_0089 (x : Var) : (nb071_alpha_dummy_036 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_036, fv_syn_cnnc] using (nb071_compact_fv_empty_0031 x)

theorem nb071_compact_envfresh_0005 (x : Var) : TEnvFresh [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_017) (nb071_alpha_dummy_018 x) (nb071_wpp_notmem_0052) (nb071_wpp_notmem_0053 x) (TEnvFresh.consFresh (nb071_alpha_dummy_013) (nb071_alpha_dummy_015 x) (nb071_wpp_notmem_0054) (nb071_wpp_notmem_0055 x) (TEnvFresh.consFresh (nb071_alpha_dummy_014) (nb071_alpha_dummy_016 x) (nb071_wpp_notmem_0056) (nb071_wpp_notmem_0057 x) (TEnvFresh.consFresh (nb071_alpha_dummy_039) (nb071_alpha_dummy_040 x) (nb071_wpp_notmem_0084) (nb071_wpp_notmem_0085 x) (TEnvFresh.consFresh (nb071_alpha_dummy_037) (nb071_alpha_dummy_038 x) (nb071_wpp_notmem_0086) (nb071_wpp_notmem_0087 x) (TEnvFresh.consFresh (nb071_alpha_dummy_006) (nb071_alpha_dummy_008 x) (nb071_wpp_notmem_0058) (nb071_wpp_notmem_0059 x) (TEnvFresh.consFresh (nb071_alpha_dummy_005) (nb071_alpha_dummy_007 x) (nb071_wpp_notmem_0060) (nb071_wpp_notmem_0061 x) (TEnvFresh.consFresh (nb071_alpha_dummy_035) (nb071_alpha_dummy_036 x) (nb071_wpp_notmem_0088) (nb071_wpp_notmem_0089 x) (TEnvFresh.consFresh (nb071_alpha_dummy_009) (nb071_alpha_dummy_010 x) (nb071_wpp_notmem_0064) (nb071_wpp_notmem_0065 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0066) (nb071_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0068) (nb071_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0070) (nb071_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb071_wpp_refl_0005 (x : Var) : TReflOn [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0005 x)

noncomputable def nb071_split_alpha_0003 (x : Var) : TAlphaWff [((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (Wff.classMem (Class.cv (nb071_alpha_dummy_039)) (syn_cphi (Class.cv (nb071_alpha_dummy_006)))) (Wff.classMem (Class.cv (nb071_alpha_dummy_040 x)) (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0013 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0042) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0043 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0041 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0016) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0017 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)), ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_c1c) (nb071_wpp_refl_0003 x))) (TAlphaWff.neg (TAlphaWff.neg (nb071_split_alpha_0002 x)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_cnnc) (nb071_wpp_refl_0005 x))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)), ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)), ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_cnnc) (nb071_wpp_refl_0005 x))))))))))))))))))

theorem nb071_wpp_notmem_0090 : (nb071_alpha_dummy_037) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0028)

theorem nb071_wpp_notmem_0091 (x : Var) : (nb071_alpha_dummy_038 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0029 x)

theorem nb071_wpp_notmem_0092 : (nb071_alpha_dummy_006) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0012)

theorem nb071_wpp_notmem_0093 (x : Var) : (nb071_alpha_dummy_008 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0013 x)

theorem nb071_wpp_notmem_0094 : (nb071_alpha_dummy_005) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0014)

theorem nb071_wpp_notmem_0095 (x : Var) : (nb071_alpha_dummy_007 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0015 x)

theorem nb071_wpp_notmem_0096 : (nb071_alpha_dummy_035) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0030)

theorem nb071_wpp_notmem_0097 (x : Var) : (nb071_alpha_dummy_036 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_036, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0031 x)

theorem nb071_wpp_notmem_0098 : (nb071_alpha_dummy_009) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0018)

theorem nb071_wpp_notmem_0099 (x : Var) : (nb071_alpha_dummy_010 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0019 x)

theorem nb071_wpp_notmem_0100 : (nb071_alpha_dummy_001) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0020)

theorem nb071_wpp_notmem_0101 (x : Var) : (nb071_alpha_dummy_002 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0021 x)

theorem nb071_wpp_notmem_0102 : (nb071_alpha_dummy_000) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0022)

theorem nb071_wpp_notmem_0103 (x : Var) : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0023 x)

theorem nb071_wpp_notmem_0104 : (nb071_alpha_dummy_003) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0024)

theorem nb071_wpp_notmem_0105 (x : Var) : (nb071_alpha_dummy_004 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb071_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb071_compact_fv_empty_0025 x)

theorem nb071_compact_envfresh_0006 (x : Var) : TEnvFresh [((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_037) (nb071_alpha_dummy_038 x) (nb071_wpp_notmem_0090) (nb071_wpp_notmem_0091 x) (TEnvFresh.consFresh (nb071_alpha_dummy_006) (nb071_alpha_dummy_008 x) (nb071_wpp_notmem_0092) (nb071_wpp_notmem_0093 x) (TEnvFresh.consFresh (nb071_alpha_dummy_005) (nb071_alpha_dummy_007 x) (nb071_wpp_notmem_0094) (nb071_wpp_notmem_0095 x) (TEnvFresh.consFresh (nb071_alpha_dummy_035) (nb071_alpha_dummy_036 x) (nb071_wpp_notmem_0096) (nb071_wpp_notmem_0097 x) (TEnvFresh.consFresh (nb071_alpha_dummy_009) (nb071_alpha_dummy_010 x) (nb071_wpp_notmem_0098) (nb071_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0100) (nb071_wpp_notmem_0101 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0102) (nb071_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0104) (nb071_wpp_notmem_0105 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb071_wpp_refl_0006 (x : Var) : TReflOn [((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0006 x)

noncomputable def nb071_split_alpha_0004 (x : Var) : TAlphaWff [((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (Wff.classEq (Class.cv (nb071_alpha_dummy_003)) (syn_cop (Class.cv (nb071_alpha_dummy_000)) (Class.cv (nb071_alpha_dummy_001)))) (Wff.classEq (Class.cv (nb071_alpha_dummy_004 x)) (syn_cop (Class.cv x) (Class.cv (nb071_alpha_dummy_002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0002) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0003 x) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0000) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0001 x) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb071_split_alpha_0001 x))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb071_split_alpha_0001 x))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0039 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0035) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0037 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (nb071_split_alpha_0003 x) (TAlphaWff.neg (nb071_split_alpha_0003 x))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_ccompl (syn_csn (syn_c0c))) (nb071_wpp_refl_0006 x))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0039 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0035) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0037 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (nb071_split_alpha_0003 x) (TAlphaWff.neg (nb071_split_alpha_0003 x))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)), ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)), ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_ccompl (syn_csn (syn_c0c))) (nb071_wpp_refl_0006 x)))))))))))))))))))))))))))))

theorem nb071_compact_envfresh_0007 (x : Var) : TEnvFresh [((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0020) (nb071_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0022) (nb071_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0024) (nb071_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))

noncomputable def nb071_wpp_refl_0007 (x : Var) : TReflOn [((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0007 x)

theorem nb071_compact_fv_empty_0032 : (nb071_alpha_dummy_041) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0106 : (nb071_alpha_dummy_041) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_041, fv_syn_cncs] using (nb071_compact_fv_empty_0032)

theorem nb071_compact_fv_empty_0033 (x : Var) : (nb071_alpha_dummy_043 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0107 (x : Var) : (nb071_alpha_dummy_043 x) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_043, fv_syn_cncs] using (nb071_compact_fv_empty_0033 x)

theorem nb071_compact_fv_empty_0034 : (nb071_alpha_dummy_045) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0108 : (nb071_alpha_dummy_045) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_045, fv_syn_cncs] using (nb071_compact_fv_empty_0034)

theorem nb071_compact_fv_empty_0035 (x : Var) : (nb071_alpha_dummy_046 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0109 (x : Var) : (nb071_alpha_dummy_046 x) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_046, fv_syn_cncs] using (nb071_compact_fv_empty_0035 x)

theorem nb071_compact_fv_empty_0036 : (nb071_alpha_dummy_048) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0110 : (nb071_alpha_dummy_048) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_048, fv_syn_cncs] using (nb071_compact_fv_empty_0036)

theorem nb071_compact_fv_empty_0037 (x : Var) : (nb071_alpha_dummy_050 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0111 (x : Var) : (nb071_alpha_dummy_050 x) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_050, fv_syn_cncs] using (nb071_compact_fv_empty_0037 x)

theorem nb071_compact_fv_empty_0038 : (nb071_alpha_dummy_047) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0112 : (nb071_alpha_dummy_047) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_047, fv_syn_cncs] using (nb071_compact_fv_empty_0038)

theorem nb071_compact_fv_empty_0039 (x : Var) : (nb071_alpha_dummy_049 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0113 (x : Var) : (nb071_alpha_dummy_049 x) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_049, fv_syn_cncs] using (nb071_compact_fv_empty_0039 x)

theorem nb071_wpp_notmem_0114 : (nb071_alpha_dummy_001) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_001, fv_syn_cncs] using (nb071_compact_fv_empty_0020)

theorem nb071_wpp_notmem_0115 (x : Var) : (nb071_alpha_dummy_002 x) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_002, fv_syn_cncs] using (nb071_compact_fv_empty_0021 x)

theorem nb071_wpp_notmem_0116 : (nb071_alpha_dummy_000) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_000, fv_syn_cncs] using (nb071_compact_fv_empty_0022)

theorem nb071_wpp_notmem_0117 (x : Var) : x ∉ ((syn_cncs)).fv := by
  simpa only [fv_syn_cncs] using (nb071_compact_fv_empty_0023 x)

theorem nb071_wpp_notmem_0118 : (nb071_alpha_dummy_003) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_003, fv_syn_cncs] using (nb071_compact_fv_empty_0024)

theorem nb071_wpp_notmem_0119 (x : Var) : (nb071_alpha_dummy_004 x) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_004, fv_syn_cncs] using (nb071_compact_fv_empty_0025 x)

theorem nb071_compact_envfresh_0008 (x : Var) : TEnvFresh [((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_cncs)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_041) (nb071_alpha_dummy_043 x) (nb071_wpp_notmem_0106) (nb071_wpp_notmem_0107 x) (TEnvFresh.consFresh (nb071_alpha_dummy_045) (nb071_alpha_dummy_046 x) (nb071_wpp_notmem_0108) (nb071_wpp_notmem_0109 x) (TEnvFresh.consFresh (nb071_alpha_dummy_048) (nb071_alpha_dummy_050 x) (nb071_wpp_notmem_0110) (nb071_wpp_notmem_0111 x) (TEnvFresh.consFresh (nb071_alpha_dummy_047) (nb071_alpha_dummy_049 x) (nb071_wpp_notmem_0112) (nb071_wpp_notmem_0113 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0114) (nb071_wpp_notmem_0115 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0116) (nb071_wpp_notmem_0117 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0118) (nb071_wpp_notmem_0119 x) (TEnvFresh.nil ((syn_cncs)).fv))))))))

noncomputable def nb071_wpp_refl_0008 (x : Var) : TReflOn [((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_cncs)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0008 x)

theorem nb071_compact_fv_empty_0040 : (nb071_alpha_dummy_063) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0120 : (nb071_alpha_dummy_063) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_063, fv_syn_c1c] using (nb071_compact_fv_empty_0040)

theorem nb071_compact_fv_empty_0041 (x : Var) : (nb071_alpha_dummy_064 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0121 (x : Var) : (nb071_alpha_dummy_064 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_064, fv_syn_c1c] using (nb071_compact_fv_empty_0041 x)

theorem nb071_compact_fv_empty_0042 : (nb071_alpha_dummy_061) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0122 : (nb071_alpha_dummy_061) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_061, fv_syn_c1c] using (nb071_compact_fv_empty_0042)

theorem nb071_compact_fv_empty_0043 (x : Var) : (nb071_alpha_dummy_062 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0123 (x : Var) : (nb071_alpha_dummy_062 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_062, fv_syn_c1c] using (nb071_compact_fv_empty_0043 x)

theorem nb071_compact_fv_empty_0044 : (nb071_alpha_dummy_059) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0124 : (nb071_alpha_dummy_059) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_059, fv_syn_c1c] using (nb071_compact_fv_empty_0044)

theorem nb071_compact_fv_empty_0045 (x : Var) : (nb071_alpha_dummy_060 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0125 (x : Var) : (nb071_alpha_dummy_060 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_060, fv_syn_c1c] using (nb071_compact_fv_empty_0045 x)

theorem nb071_compact_fv_empty_0046 : (nb071_alpha_dummy_056) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0126 : (nb071_alpha_dummy_056) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_056, fv_syn_c1c] using (nb071_compact_fv_empty_0046)

theorem nb071_compact_fv_empty_0047 (x : Var) : (nb071_alpha_dummy_058 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0127 (x : Var) : (nb071_alpha_dummy_058 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_058, fv_syn_c1c] using (nb071_compact_fv_empty_0047 x)

theorem nb071_compact_fv_empty_0048 : (nb071_alpha_dummy_055) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0128 : (nb071_alpha_dummy_055) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_055, fv_syn_c1c] using (nb071_compact_fv_empty_0048)

theorem nb071_compact_fv_empty_0049 (x : Var) : (nb071_alpha_dummy_057 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0129 (x : Var) : (nb071_alpha_dummy_057 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_057, fv_syn_c1c] using (nb071_compact_fv_empty_0049 x)

theorem nb071_compact_fv_empty_0050 : (nb071_alpha_dummy_042) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0130 : (nb071_alpha_dummy_042) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_042, fv_syn_c1c] using (nb071_compact_fv_empty_0050)

theorem nb071_compact_fv_empty_0051 (x : Var) : (nb071_alpha_dummy_044 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0131 (x : Var) : (nb071_alpha_dummy_044 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_044, fv_syn_c1c] using (nb071_compact_fv_empty_0051 x)

theorem nb071_wpp_notmem_0132 : (nb071_alpha_dummy_041) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_041, fv_syn_c1c] using (nb071_compact_fv_empty_0032)

theorem nb071_wpp_notmem_0133 (x : Var) : (nb071_alpha_dummy_043 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_043, fv_syn_c1c] using (nb071_compact_fv_empty_0033 x)

theorem nb071_wpp_notmem_0134 : (nb071_alpha_dummy_045) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_045, fv_syn_c1c] using (nb071_compact_fv_empty_0034)

theorem nb071_wpp_notmem_0135 (x : Var) : (nb071_alpha_dummy_046 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_046, fv_syn_c1c] using (nb071_compact_fv_empty_0035 x)

theorem nb071_wpp_notmem_0136 : (nb071_alpha_dummy_048) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_048, fv_syn_c1c] using (nb071_compact_fv_empty_0036)

theorem nb071_wpp_notmem_0137 (x : Var) : (nb071_alpha_dummy_050 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_050, fv_syn_c1c] using (nb071_compact_fv_empty_0037 x)

theorem nb071_wpp_notmem_0138 : (nb071_alpha_dummy_047) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_047, fv_syn_c1c] using (nb071_compact_fv_empty_0038)

theorem nb071_wpp_notmem_0139 (x : Var) : (nb071_alpha_dummy_049 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_049, fv_syn_c1c] using (nb071_compact_fv_empty_0039 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
