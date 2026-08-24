import NAR4C072C001Part005

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

theorem nb072_wpp_notmem_0078 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_036 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_036, fv_syn_cnnc] using (nb072_compact_fv_empty_0024 A B R S_cls H)

theorem nb072_wpp_notmem_0079 (x : Var) (y : Var) : (nb072_alpha_dummy_037 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_037, fv_syn_cnnc] using (nb072_compact_fv_empty_0025 x y)

theorem nb072_wpp_notmem_0080 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_034 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_034, fv_syn_cnnc] using (nb072_compact_fv_empty_0026 A B R S_cls H)

theorem nb072_wpp_notmem_0081 (x : Var) (y : Var) : (nb072_alpha_dummy_035 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_035, fv_syn_cnnc] using (nb072_compact_fv_empty_0027 x y)

theorem nb072_wpp_notmem_0082 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_032 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_032, fv_syn_cnnc] using (nb072_compact_fv_empty_0028 A B R S_cls H)

theorem nb072_wpp_notmem_0083 (x : Var) (y : Var) : (nb072_alpha_dummy_033 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_033, fv_syn_cnnc] using (nb072_compact_fv_empty_0029 x y)

theorem nb072_compact_envfresh_0008 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TEnvFresh [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)), ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)), ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)), ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)), ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)), ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)), ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)), ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)), ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb072_alpha_dummy_014 A B R S_cls H) (nb072_alpha_dummy_015 x y) (nb072_wpp_notmem_0048 A B R S_cls H) (nb072_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_010 A B R S_cls H) (nb072_alpha_dummy_012 x y) (nb072_wpp_notmem_0050 A B R S_cls H) (nb072_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_011 A B R S_cls H) (nb072_alpha_dummy_013 x y) (nb072_wpp_notmem_0052 A B R S_cls H) (nb072_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_036 A B R S_cls H) (nb072_alpha_dummy_037 x y) (nb072_wpp_notmem_0078 A B R S_cls H) (nb072_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_034 A B R S_cls H) (nb072_alpha_dummy_035 x y) (nb072_wpp_notmem_0080 A B R S_cls H) (nb072_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_003 A B R S_cls H) (nb072_alpha_dummy_005 x y) (nb072_wpp_notmem_0054 A B R S_cls H) (nb072_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_002 A B R S_cls H) (nb072_alpha_dummy_004 x y) (nb072_wpp_notmem_0056 A B R S_cls H) (nb072_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_032 A B R S_cls H) (nb072_alpha_dummy_033 x y) (nb072_wpp_notmem_0082 A B R S_cls H) (nb072_wpp_notmem_0083 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_006 A B R S_cls H) (nb072_alpha_dummy_007 x y) (nb072_wpp_notmem_0060 A B R S_cls H) (nb072_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y (nb072_wpp_notmem_0062 A B R S_cls H) (nb072_wpp_notmem_0063 y) (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x (nb072_wpp_notmem_0064 A B R S_cls H) (nb072_wpp_notmem_0065 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))

noncomputable def nb072_wpp_refl_0006 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TReflOn [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)), ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)), ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)), ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)), ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)), ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)), ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)), ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)), ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0008 x y A B R S_cls H)

theorem nb072_wpp_notmem_0084 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_034 A B R S_cls H) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_034, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0026 A B R S_cls H)

theorem nb072_wpp_notmem_0085 (x : Var) (y : Var) : (nb072_alpha_dummy_035 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0027 x y)

theorem nb072_wpp_notmem_0086 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_003 A B R S_cls H) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0012 A B R S_cls H)

theorem nb072_wpp_notmem_0087 (x : Var) (y : Var) : (nb072_alpha_dummy_005 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0013 x y)

theorem nb072_wpp_notmem_0088 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_002 A B R S_cls H) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0014 A B R S_cls H)

theorem nb072_wpp_notmem_0089 (x : Var) (y : Var) : (nb072_alpha_dummy_004 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0015 x y)

theorem nb072_wpp_notmem_0090 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_032 A B R S_cls H) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_032, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0028 A B R S_cls H)

theorem nb072_wpp_notmem_0091 (x : Var) (y : Var) : (nb072_alpha_dummy_033 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_033, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0029 x y)

theorem nb072_wpp_notmem_0092 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_006 A B R S_cls H) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0018 A B R S_cls H)

theorem nb072_wpp_notmem_0093 (x : Var) (y : Var) : (nb072_alpha_dummy_007 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0019 x y)

theorem nb072_wpp_notmem_0094 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0020 A B R S_cls H)

theorem nb072_wpp_notmem_0095 (y : Var) : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0021 y)

theorem nb072_wpp_notmem_0096 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb072_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0022 A B R S_cls H)

theorem nb072_wpp_notmem_0097 (x : Var) : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb072_compact_fv_empty_0023 x)

theorem nb072_compact_envfresh_0009 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TEnvFresh [((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)), ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)), ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)), ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)), ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb072_alpha_dummy_034 A B R S_cls H) (nb072_alpha_dummy_035 x y) (nb072_wpp_notmem_0084 A B R S_cls H) (nb072_wpp_notmem_0085 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_003 A B R S_cls H) (nb072_alpha_dummy_005 x y) (nb072_wpp_notmem_0086 A B R S_cls H) (nb072_wpp_notmem_0087 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_002 A B R S_cls H) (nb072_alpha_dummy_004 x y) (nb072_wpp_notmem_0088 A B R S_cls H) (nb072_wpp_notmem_0089 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_032 A B R S_cls H) (nb072_alpha_dummy_033 x y) (nb072_wpp_notmem_0090 A B R S_cls H) (nb072_wpp_notmem_0091 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_006 A B R S_cls H) (nb072_alpha_dummy_007 x y) (nb072_wpp_notmem_0092 A B R S_cls H) (nb072_wpp_notmem_0093 x y) (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y (nb072_wpp_notmem_0094 A B R S_cls H) (nb072_wpp_notmem_0095 y) (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x (nb072_wpp_notmem_0096 A B R S_cls H) (nb072_wpp_notmem_0097 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))

noncomputable def nb072_wpp_refl_0007 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TReflOn [((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)), ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)), ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)), ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)), ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0009 x y A B R S_cls H)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
