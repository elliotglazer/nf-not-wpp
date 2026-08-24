import NAR4C068C001Part013

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

theorem nb068_wpp_notmem_0067 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb068_compact_fv_empty_0021 y)

theorem nb068_wpp_notmem_0068 : (nb068_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_001, fv_syn_cnnc] using (nb068_compact_fv_empty_0022)

theorem nb068_wpp_notmem_0069 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb068_compact_fv_empty_0023 x)

theorem nb068_wpp_notmem_0070 : (nb068_alpha_dummy_003) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_003, fv_syn_cnnc] using (nb068_compact_fv_empty_0024)

theorem nb068_wpp_notmem_0071 (x : Var) (y : Var) (f : Var) : (nb068_alpha_dummy_004 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_004, fv_syn_cnnc] using (nb068_compact_fv_empty_0025 x y f)

theorem nb068_compact_envfresh_0002 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_017) (nb068_alpha_dummy_018 x y) (nb068_wpp_notmem_0052) (nb068_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_013) (nb068_alpha_dummy_015 x y) (nb068_wpp_notmem_0054) (nb068_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_014) (nb068_alpha_dummy_016 x y) (nb068_wpp_notmem_0056) (nb068_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_006) (nb068_alpha_dummy_008 x y) (nb068_wpp_notmem_0058) (nb068_wpp_notmem_0059 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_005) (nb068_alpha_dummy_007 x y) (nb068_wpp_notmem_0060) (nb068_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_011) (nb068_alpha_dummy_012 x y) (nb068_wpp_notmem_0062) (nb068_wpp_notmem_0063 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_009) (nb068_alpha_dummy_010 x y) (nb068_wpp_notmem_0064) (nb068_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb068_wpp_refl_0002 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0002 x y f)

noncomputable def nb068_split_alpha_0001 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) : TAlphaWff [((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_006)) (Class.cv (nb068_alpha_dummy_001))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_008 x y)) (Class.cv x)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0009 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0005) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0007 x y) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0011 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0011 x y) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_008 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0015 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0000 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0000 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0002 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0002 x y f))))))))))))))))))))

theorem nb068_compact_fv_empty_0026 : (nb068_alpha_dummy_039) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0072 : (nb068_alpha_dummy_039) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_039, fv_syn_c1c] using (nb068_compact_fv_empty_0026)

theorem nb068_compact_fv_empty_0027 (x : Var) (y : Var) : (nb068_alpha_dummy_040 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0073 (x : Var) (y : Var) : (nb068_alpha_dummy_040 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_040, fv_syn_c1c] using (nb068_compact_fv_empty_0027 x y)

theorem nb068_compact_fv_empty_0028 : (nb068_alpha_dummy_037) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0074 : (nb068_alpha_dummy_037) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_037, fv_syn_c1c] using (nb068_compact_fv_empty_0028)

theorem nb068_compact_fv_empty_0029 (x : Var) (y : Var) : (nb068_alpha_dummy_038 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0075 (x : Var) (y : Var) : (nb068_alpha_dummy_038 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_038, fv_syn_c1c] using (nb068_compact_fv_empty_0029 x y)

theorem nb068_compact_fv_empty_0030 : (nb068_alpha_dummy_035) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0076 : (nb068_alpha_dummy_035) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_035, fv_syn_c1c] using (nb068_compact_fv_empty_0030)

theorem nb068_compact_fv_empty_0031 (x : Var) (y : Var) : (nb068_alpha_dummy_036 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0077 (x : Var) (y : Var) : (nb068_alpha_dummy_036 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_036, fv_syn_c1c] using (nb068_compact_fv_empty_0031 x y)

theorem nb068_compact_envfresh_0003 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_021) (nb068_alpha_dummy_024 x y) (nb068_wpp_notmem_0000) (nb068_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_020) (nb068_alpha_dummy_023 x y) (nb068_wpp_notmem_0002) (nb068_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_019) (nb068_alpha_dummy_022 x y) (nb068_wpp_notmem_0004) (nb068_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_017) (nb068_alpha_dummy_018 x y) (nb068_wpp_notmem_0006) (nb068_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_013) (nb068_alpha_dummy_015 x y) (nb068_wpp_notmem_0008) (nb068_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_014) (nb068_alpha_dummy_016 x y) (nb068_wpp_notmem_0010) (nb068_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_039) (nb068_alpha_dummy_040 x y) (nb068_wpp_notmem_0072) (nb068_wpp_notmem_0073 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_037) (nb068_alpha_dummy_038 x y) (nb068_wpp_notmem_0074) (nb068_wpp_notmem_0075 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_006) (nb068_alpha_dummy_008 x y) (nb068_wpp_notmem_0012) (nb068_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_005) (nb068_alpha_dummy_007 x y) (nb068_wpp_notmem_0014) (nb068_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_035) (nb068_alpha_dummy_036 x y) (nb068_wpp_notmem_0076) (nb068_wpp_notmem_0077 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_009) (nb068_alpha_dummy_010 x y) (nb068_wpp_notmem_0018) (nb068_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb068_wpp_refl_0003 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0003 x y f)

theorem nb068_wpp_notmem_0078 : (nb068_alpha_dummy_039) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_039, fv_syn_c0] using (nb068_compact_fv_empty_0026)

theorem nb068_wpp_notmem_0079 (x : Var) (y : Var) : (nb068_alpha_dummy_040 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_040, fv_syn_c0] using (nb068_compact_fv_empty_0027 x y)

theorem nb068_wpp_notmem_0080 : (nb068_alpha_dummy_037) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_037, fv_syn_c0] using (nb068_compact_fv_empty_0028)

theorem nb068_wpp_notmem_0081 (x : Var) (y : Var) : (nb068_alpha_dummy_038 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_038, fv_syn_c0] using (nb068_compact_fv_empty_0029 x y)

theorem nb068_wpp_notmem_0082 : (nb068_alpha_dummy_035) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_035, fv_syn_c0] using (nb068_compact_fv_empty_0030)

theorem nb068_wpp_notmem_0083 (x : Var) (y : Var) : (nb068_alpha_dummy_036 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_036, fv_syn_c0] using (nb068_compact_fv_empty_0031 x y)

theorem nb068_compact_envfresh_0004 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_021) (nb068_alpha_dummy_024 x y) (nb068_wpp_notmem_0026) (nb068_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_020) (nb068_alpha_dummy_023 x y) (nb068_wpp_notmem_0028) (nb068_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_019) (nb068_alpha_dummy_022 x y) (nb068_wpp_notmem_0030) (nb068_wpp_notmem_0031 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_017) (nb068_alpha_dummy_018 x y) (nb068_wpp_notmem_0032) (nb068_wpp_notmem_0033 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_013) (nb068_alpha_dummy_015 x y) (nb068_wpp_notmem_0034) (nb068_wpp_notmem_0035 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_014) (nb068_alpha_dummy_016 x y) (nb068_wpp_notmem_0036) (nb068_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_039) (nb068_alpha_dummy_040 x y) (nb068_wpp_notmem_0078) (nb068_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_037) (nb068_alpha_dummy_038 x y) (nb068_wpp_notmem_0080) (nb068_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_006) (nb068_alpha_dummy_008 x y) (nb068_wpp_notmem_0038) (nb068_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_005) (nb068_alpha_dummy_007 x y) (nb068_wpp_notmem_0040) (nb068_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_035) (nb068_alpha_dummy_036 x y) (nb068_wpp_notmem_0082) (nb068_wpp_notmem_0083 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_009) (nb068_alpha_dummy_010 x y) (nb068_wpp_notmem_0044) (nb068_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb068_wpp_refl_0004 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0004 x y f)

noncomputable def nb068_split_alpha_0002 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_019)) (syn_cun (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_022 x y)) (syn_cun (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0017 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0023 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0021 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0017 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0023 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0021 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0004 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0027 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0025 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0027 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0025 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0031 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0029 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0031 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0029 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_0084 : (nb068_alpha_dummy_039) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_039, fv_syn_cnnc] using (nb068_compact_fv_empty_0026)

theorem nb068_wpp_notmem_0085 (x : Var) (y : Var) : (nb068_alpha_dummy_040 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_040, fv_syn_cnnc] using (nb068_compact_fv_empty_0027 x y)

theorem nb068_wpp_notmem_0086 : (nb068_alpha_dummy_037) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_037, fv_syn_cnnc] using (nb068_compact_fv_empty_0028)

theorem nb068_wpp_notmem_0087 (x : Var) (y : Var) : (nb068_alpha_dummy_038 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_038, fv_syn_cnnc] using (nb068_compact_fv_empty_0029 x y)

theorem nb068_wpp_notmem_0088 : (nb068_alpha_dummy_035) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_035, fv_syn_cnnc] using (nb068_compact_fv_empty_0030)

theorem nb068_wpp_notmem_0089 (x : Var) (y : Var) : (nb068_alpha_dummy_036 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_036, fv_syn_cnnc] using (nb068_compact_fv_empty_0031 x y)

theorem nb068_compact_envfresh_0005 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_017) (nb068_alpha_dummy_018 x y) (nb068_wpp_notmem_0052) (nb068_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_013) (nb068_alpha_dummy_015 x y) (nb068_wpp_notmem_0054) (nb068_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_014) (nb068_alpha_dummy_016 x y) (nb068_wpp_notmem_0056) (nb068_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_039) (nb068_alpha_dummy_040 x y) (nb068_wpp_notmem_0084) (nb068_wpp_notmem_0085 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_037) (nb068_alpha_dummy_038 x y) (nb068_wpp_notmem_0086) (nb068_wpp_notmem_0087 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_006) (nb068_alpha_dummy_008 x y) (nb068_wpp_notmem_0058) (nb068_wpp_notmem_0059 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_005) (nb068_alpha_dummy_007 x y) (nb068_wpp_notmem_0060) (nb068_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_035) (nb068_alpha_dummy_036 x y) (nb068_wpp_notmem_0088) (nb068_wpp_notmem_0089 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_009) (nb068_alpha_dummy_010 x y) (nb068_wpp_notmem_0064) (nb068_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb068_wpp_refl_0005 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0005 x y f)

noncomputable def nb068_split_alpha_0003 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_039)) (syn_cphi (Class.cv (nb068_alpha_dummy_006)))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_039)) (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_040 x y)) (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_040 x y)) (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0011 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0011 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_008 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0015 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0003 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0002 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0005 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0005 x y f)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0011 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0011 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0041 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0039 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_008 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0015 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0003 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0002 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0005 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0005 x y f))))))))))))))))))))

theorem nb068_wpp_notmem_0090 : (nb068_alpha_dummy_037) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0028)

theorem nb068_wpp_notmem_0091 (x : Var) (y : Var) : (nb068_alpha_dummy_038 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0029 x y)

theorem nb068_wpp_notmem_0092 : (nb068_alpha_dummy_006) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0012)

theorem nb068_wpp_notmem_0093 (x : Var) (y : Var) : (nb068_alpha_dummy_008 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0013 x y)

theorem nb068_wpp_notmem_0094 : (nb068_alpha_dummy_005) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0014)

theorem nb068_wpp_notmem_0095 (x : Var) (y : Var) : (nb068_alpha_dummy_007 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0015 x y)

theorem nb068_wpp_notmem_0096 : (nb068_alpha_dummy_035) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0030)

theorem nb068_wpp_notmem_0097 (x : Var) (y : Var) : (nb068_alpha_dummy_036 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_036, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0031 x y)

theorem nb068_wpp_notmem_0098 : (nb068_alpha_dummy_009) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0018)

theorem nb068_wpp_notmem_0099 (x : Var) (y : Var) : (nb068_alpha_dummy_010 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0019 x y)

theorem nb068_wpp_notmem_0100 : (nb068_alpha_dummy_002) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0020)

theorem nb068_wpp_notmem_0101 (y : Var) : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0021 y)

theorem nb068_wpp_notmem_0102 : (nb068_alpha_dummy_001) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0022)

theorem nb068_wpp_notmem_0103 (x : Var) : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0023 x)

theorem nb068_wpp_notmem_0104 : (nb068_alpha_dummy_003) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0024)

theorem nb068_wpp_notmem_0105 (x : Var) (y : Var) (f : Var) : (nb068_alpha_dummy_004 x y f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0025 x y f)

theorem nb068_compact_envfresh_0006 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_037) (nb068_alpha_dummy_038 x y) (nb068_wpp_notmem_0090) (nb068_wpp_notmem_0091 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_006) (nb068_alpha_dummy_008 x y) (nb068_wpp_notmem_0092) (nb068_wpp_notmem_0093 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_005) (nb068_alpha_dummy_007 x y) (nb068_wpp_notmem_0094) (nb068_wpp_notmem_0095 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_035) (nb068_alpha_dummy_036 x y) (nb068_wpp_notmem_0096) (nb068_wpp_notmem_0097 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_009) (nb068_alpha_dummy_010 x y) (nb068_wpp_notmem_0098) (nb068_wpp_notmem_0099 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0100) (nb068_wpp_notmem_0101 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0102) (nb068_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0104) (nb068_wpp_notmem_0105 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb068_wpp_refl_0006 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0006 x y f)

noncomputable def nb068_split_alpha_0004 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) : TAlphaWff [((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.classEq (Class.cv (nb068_alpha_dummy_003)) (syn_cop (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002)))) (Wff.classEq (Class.cv (nb068_alpha_dummy_004 x y f)) (syn_cop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0002) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0003 x y f) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0000) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0001 x y f) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0001 x y f dv_x_y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0001 x y f dv_x_y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0035 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0003 x y f))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0006 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0037 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0035 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0003 x y f))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0006 x y f)))))))))))))))))))))))))))))

theorem nb068_compact_fv_empty_0032 : (nb068_alpha_dummy_069) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0106 : (nb068_alpha_dummy_069) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_069, fv_syn_c1c] using (nb068_compact_fv_empty_0032)

theorem nb068_compact_fv_empty_0033 (f : Var) : (nb068_alpha_dummy_072 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0107 (f : Var) : (nb068_alpha_dummy_072 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_072, fv_syn_c1c] using (nb068_compact_fv_empty_0033 f)

theorem nb068_compact_fv_empty_0034 : (nb068_alpha_dummy_068) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0108 : (nb068_alpha_dummy_068) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_068, fv_syn_c1c] using (nb068_compact_fv_empty_0034)

theorem nb068_compact_fv_empty_0035 (f : Var) : (nb068_alpha_dummy_071 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0109 (f : Var) : (nb068_alpha_dummy_071 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_071, fv_syn_c1c] using (nb068_compact_fv_empty_0035 f)

theorem nb068_compact_fv_empty_0036 : (nb068_alpha_dummy_067) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0110 : (nb068_alpha_dummy_067) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_067, fv_syn_c1c] using (nb068_compact_fv_empty_0036)

theorem nb068_compact_fv_empty_0037 (f : Var) : (nb068_alpha_dummy_070 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0111 (f : Var) : (nb068_alpha_dummy_070 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_070, fv_syn_c1c] using (nb068_compact_fv_empty_0037 f)

theorem nb068_compact_fv_empty_0038 : (nb068_alpha_dummy_065) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0112 : (nb068_alpha_dummy_065) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_065, fv_syn_c1c] using (nb068_compact_fv_empty_0038)

theorem nb068_compact_fv_empty_0039 (f : Var) : (nb068_alpha_dummy_066 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0113 (f : Var) : (nb068_alpha_dummy_066 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_066, fv_syn_c1c] using (nb068_compact_fv_empty_0039 f)

theorem nb068_compact_fv_empty_0040 : (nb068_alpha_dummy_061) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0114 : (nb068_alpha_dummy_061) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_061, fv_syn_c1c] using (nb068_compact_fv_empty_0040)

theorem nb068_compact_fv_empty_0041 (f : Var) : (nb068_alpha_dummy_063 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0115 (f : Var) : (nb068_alpha_dummy_063 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_063, fv_syn_c1c] using (nb068_compact_fv_empty_0041 f)

theorem nb068_compact_fv_empty_0042 : (nb068_alpha_dummy_062) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0116 : (nb068_alpha_dummy_062) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_062, fv_syn_c1c] using (nb068_compact_fv_empty_0042)

theorem nb068_compact_fv_empty_0043 (f : Var) : (nb068_alpha_dummy_064 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0117 (f : Var) : (nb068_alpha_dummy_064 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_064, fv_syn_c1c] using (nb068_compact_fv_empty_0043 f)

theorem nb068_compact_fv_empty_0044 : (nb068_alpha_dummy_054) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0118 : (nb068_alpha_dummy_054) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_054, fv_syn_c1c] using (nb068_compact_fv_empty_0044)

theorem nb068_compact_fv_empty_0045 (f : Var) : (nb068_alpha_dummy_056 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0119 (f : Var) : (nb068_alpha_dummy_056 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_056, fv_syn_c1c] using (nb068_compact_fv_empty_0045 f)

theorem nb068_compact_fv_empty_0046 : (nb068_alpha_dummy_053) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0120 : (nb068_alpha_dummy_053) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_053, fv_syn_c1c] using (nb068_compact_fv_empty_0046)

theorem nb068_compact_fv_empty_0047 (f : Var) : (nb068_alpha_dummy_055 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0121 (f : Var) : (nb068_alpha_dummy_055 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_055, fv_syn_c1c] using (nb068_compact_fv_empty_0047 f)

theorem nb068_compact_fv_empty_0048 : (nb068_alpha_dummy_059) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0122 : (nb068_alpha_dummy_059) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_059, fv_syn_c1c] using (nb068_compact_fv_empty_0048)

theorem nb068_compact_fv_empty_0049 (f : Var) : (nb068_alpha_dummy_060 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0123 (f : Var) : (nb068_alpha_dummy_060 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_060, fv_syn_c1c] using (nb068_compact_fv_empty_0049 f)

theorem nb068_compact_fv_empty_0050 : (nb068_alpha_dummy_057) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0124 : (nb068_alpha_dummy_057) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_057, fv_syn_c1c] using (nb068_compact_fv_empty_0050)

theorem nb068_compact_fv_empty_0051 (f : Var) : (nb068_alpha_dummy_058 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0125 (f : Var) : (nb068_alpha_dummy_058 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_058, fv_syn_c1c] using (nb068_compact_fv_empty_0051 f)

theorem nb068_compact_fv_empty_0052 : (nb068_alpha_dummy_046) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0126 : (nb068_alpha_dummy_046) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_046, fv_syn_c1c] using (nb068_compact_fv_empty_0052)

theorem nb068_compact_fv_empty_0053 (f : Var) : (nb068_alpha_dummy_049 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0127 (f : Var) : (nb068_alpha_dummy_049 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_049, fv_syn_c1c] using (nb068_compact_fv_empty_0053 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
