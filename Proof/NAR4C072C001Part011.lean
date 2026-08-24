import NAR4C072C001Part010

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

theorem nb072_compact_envfresh_0018 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) : TEnvFresh [((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] H.fv := by
  exact (TEnvFresh.consFresh (nb072_alpha_dummy_046 A B R S_cls H) (nb072_alpha_dummy_047 x H) (nb072_focused_notmem_0004 A B R S_cls H) (nb072_focused_notmem_0005 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_048 A B R S_cls H) (nb072_alpha_dummy_049 x H) (nb072_focused_notmem_0006 A B R S_cls H) (nb072_focused_notmem_0007 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_051 A B R S_cls H) (nb072_alpha_dummy_053 x H) (nb072_focused_notmem_0008 A B R S_cls H) (nb072_focused_notmem_0009 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_050 A B R S_cls H) (nb072_alpha_dummy_052 x H) (nb072_focused_notmem_0010 A B R S_cls H) (nb072_focused_notmem_0011 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_039 A B R S_cls H) (nb072_alpha_dummy_041 x y H) (nb072_focused_notmem_0012 A B R S_cls H) (nb072_focused_notmem_0013 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_038 A B R S_cls H) (nb072_alpha_dummy_040 x y H) (nb072_focused_notmem_0014 A B R S_cls H) (nb072_focused_notmem_0015 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_044 A B R S_cls H) (nb072_alpha_dummy_045 x y H) (nb072_focused_notmem_0016 A B R S_cls H) (nb072_focused_notmem_0017 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_042 A B R S_cls H) (nb072_alpha_dummy_043 x y H) (nb072_focused_notmem_0018 A B R S_cls H) (nb072_focused_notmem_0019 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y (nb072_focused_notmem_0020 A B R S_cls H) dv_H_y (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x (nb072_focused_notmem_0021 A B R S_cls H) dv_H_x (TEnvFresh.nil H.fv)))))))))))

noncomputable def nb072_focused_refl_0003 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) : TReflOn [((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] H.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0018 x y A B R S_cls H dv_H_x dv_H_y)

theorem nb072_compact_fv_empty_0072 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_100 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0244 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_100 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_100, fv_syn_c1c] using (nb072_compact_fv_empty_0072 A B R S_cls H)

theorem nb072_compact_fv_empty_0073 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_103 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0245 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_103 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_103, fv_syn_c1c] using (nb072_compact_fv_empty_0073 x y H)

theorem nb072_compact_fv_empty_0074 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_099 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0246 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_099 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_099, fv_syn_c1c] using (nb072_compact_fv_empty_0074 A B R S_cls H)

theorem nb072_compact_fv_empty_0075 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_102 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0247 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_102 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_102, fv_syn_c1c] using (nb072_compact_fv_empty_0075 x y H)

theorem nb072_compact_fv_empty_0076 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_098 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0248 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_098 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_098, fv_syn_c1c] using (nb072_compact_fv_empty_0076 A B R S_cls H)

theorem nb072_compact_fv_empty_0077 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_101 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0249 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_101 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_101, fv_syn_c1c] using (nb072_compact_fv_empty_0077 x y H)

theorem nb072_compact_fv_empty_0078 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_096 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0250 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_096 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_096, fv_syn_c1c] using (nb072_compact_fv_empty_0078 A B R S_cls H)

theorem nb072_compact_fv_empty_0079 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_097 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0251 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_097 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_097, fv_syn_c1c] using (nb072_compact_fv_empty_0079 x y H)

theorem nb072_compact_fv_empty_0080 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_092 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0252 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_092 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_092, fv_syn_c1c] using (nb072_compact_fv_empty_0080 A B R S_cls H)

theorem nb072_compact_fv_empty_0081 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_094 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0253 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_094 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_094, fv_syn_c1c] using (nb072_compact_fv_empty_0081 x y H)

theorem nb072_compact_fv_empty_0082 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_093 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0254 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_093 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_093, fv_syn_c1c] using (nb072_compact_fv_empty_0082 A B R S_cls H)

theorem nb072_compact_fv_empty_0083 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_095 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0255 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_095 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_095, fv_syn_c1c] using (nb072_compact_fv_empty_0083 x y H)

theorem nb072_compact_envfresh_0019 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TEnvFresh [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)), ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)), ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)), ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)), ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)), ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb072_alpha_dummy_100 A B R S_cls H) (nb072_alpha_dummy_103 x y H) (nb072_wpp_notmem_0244 A B R S_cls H) (nb072_wpp_notmem_0245 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_099 A B R S_cls H) (nb072_alpha_dummy_102 x y H) (nb072_wpp_notmem_0246 A B R S_cls H) (nb072_wpp_notmem_0247 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_098 A B R S_cls H) (nb072_alpha_dummy_101 x y H) (nb072_wpp_notmem_0248 A B R S_cls H) (nb072_wpp_notmem_0249 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_096 A B R S_cls H) (nb072_alpha_dummy_097 x y H) (nb072_wpp_notmem_0250 A B R S_cls H) (nb072_wpp_notmem_0251 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_092 A B R S_cls H) (nb072_alpha_dummy_094 x y H) (nb072_wpp_notmem_0252 A B R S_cls H) (nb072_wpp_notmem_0253 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_093 A B R S_cls H) (nb072_alpha_dummy_095 x y H) (nb072_wpp_notmem_0254 A B R S_cls H) (nb072_wpp_notmem_0255 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_039 A B R S_cls H) (nb072_alpha_dummy_041 x y H) (nb072_wpp_notmem_0126 A B R S_cls H) (nb072_wpp_notmem_0127 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_038 A B R S_cls H) (nb072_alpha_dummy_040 x y H) (nb072_wpp_notmem_0128 A B R S_cls H) (nb072_wpp_notmem_0129 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_044 A B R S_cls H) (nb072_alpha_dummy_045 x y H) (nb072_wpp_notmem_0130 A B R S_cls H) (nb072_wpp_notmem_0131 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_042 A B R S_cls H) (nb072_alpha_dummy_043 x y H) (nb072_wpp_notmem_0132 A B R S_cls H) (nb072_wpp_notmem_0133 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y (nb072_wpp_notmem_0020 A B R S_cls H) (nb072_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x (nb072_wpp_notmem_0022 A B R S_cls H) (nb072_wpp_notmem_0023 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))

noncomputable def nb072_wpp_refl_0015 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TReflOn [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)), ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)), ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)), ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)), ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)), ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0019 x y A B R S_cls H)

theorem nb072_wpp_notmem_0256 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_100 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_100, fv_syn_c0] using (nb072_compact_fv_empty_0072 A B R S_cls H)

theorem nb072_wpp_notmem_0257 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_103 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_103, fv_syn_c0] using (nb072_compact_fv_empty_0073 x y H)

theorem nb072_wpp_notmem_0258 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_099 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_099, fv_syn_c0] using (nb072_compact_fv_empty_0074 A B R S_cls H)

theorem nb072_wpp_notmem_0259 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_102 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_102, fv_syn_c0] using (nb072_compact_fv_empty_0075 x y H)

theorem nb072_wpp_notmem_0260 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_098 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_098, fv_syn_c0] using (nb072_compact_fv_empty_0076 A B R S_cls H)

theorem nb072_wpp_notmem_0261 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_101 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_101, fv_syn_c0] using (nb072_compact_fv_empty_0077 x y H)

theorem nb072_wpp_notmem_0262 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_096 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_096, fv_syn_c0] using (nb072_compact_fv_empty_0078 A B R S_cls H)

theorem nb072_wpp_notmem_0263 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_097 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_097, fv_syn_c0] using (nb072_compact_fv_empty_0079 x y H)

theorem nb072_wpp_notmem_0264 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_092 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_092, fv_syn_c0] using (nb072_compact_fv_empty_0080 A B R S_cls H)

theorem nb072_wpp_notmem_0265 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_094 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_094, fv_syn_c0] using (nb072_compact_fv_empty_0081 x y H)

theorem nb072_wpp_notmem_0266 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_093 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_093, fv_syn_c0] using (nb072_compact_fv_empty_0082 A B R S_cls H)

theorem nb072_wpp_notmem_0267 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_095 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_095, fv_syn_c0] using (nb072_compact_fv_empty_0083 x y H)

theorem nb072_compact_envfresh_0020 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TEnvFresh [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)), ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)), ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)), ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)), ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)), ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb072_alpha_dummy_100 A B R S_cls H) (nb072_alpha_dummy_103 x y H) (nb072_wpp_notmem_0256 A B R S_cls H) (nb072_wpp_notmem_0257 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_099 A B R S_cls H) (nb072_alpha_dummy_102 x y H) (nb072_wpp_notmem_0258 A B R S_cls H) (nb072_wpp_notmem_0259 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_098 A B R S_cls H) (nb072_alpha_dummy_101 x y H) (nb072_wpp_notmem_0260 A B R S_cls H) (nb072_wpp_notmem_0261 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_096 A B R S_cls H) (nb072_alpha_dummy_097 x y H) (nb072_wpp_notmem_0262 A B R S_cls H) (nb072_wpp_notmem_0263 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_092 A B R S_cls H) (nb072_alpha_dummy_094 x y H) (nb072_wpp_notmem_0264 A B R S_cls H) (nb072_wpp_notmem_0265 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_093 A B R S_cls H) (nb072_alpha_dummy_095 x y H) (nb072_wpp_notmem_0266 A B R S_cls H) (nb072_wpp_notmem_0267 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_039 A B R S_cls H) (nb072_alpha_dummy_041 x y H) (nb072_wpp_notmem_0162 A B R S_cls H) (nb072_wpp_notmem_0163 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_038 A B R S_cls H) (nb072_alpha_dummy_040 x y H) (nb072_wpp_notmem_0164 A B R S_cls H) (nb072_wpp_notmem_0165 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_044 A B R S_cls H) (nb072_alpha_dummy_045 x y H) (nb072_wpp_notmem_0166 A B R S_cls H) (nb072_wpp_notmem_0167 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_042 A B R S_cls H) (nb072_alpha_dummy_043 x y H) (nb072_wpp_notmem_0168 A B R S_cls H) (nb072_wpp_notmem_0169 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y (nb072_wpp_notmem_0044 A B R S_cls H) (nb072_wpp_notmem_0045 y) (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x (nb072_wpp_notmem_0046 A B R S_cls H) (nb072_wpp_notmem_0047 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))

noncomputable def nb072_wpp_refl_0016 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TReflOn [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)), ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)), ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)), ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)), ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)), ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0020 x y A B R S_cls H)

theorem nb072_wpp_notmem_0268 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_096 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_096, fv_syn_cnnc] using (nb072_compact_fv_empty_0078 A B R S_cls H)

theorem nb072_wpp_notmem_0269 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_097 x y H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_097, fv_syn_cnnc] using (nb072_compact_fv_empty_0079 x y H)

theorem nb072_wpp_notmem_0270 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_092 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_092, fv_syn_cnnc] using (nb072_compact_fv_empty_0080 A B R S_cls H)

theorem nb072_wpp_notmem_0271 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_094 x y H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_094, fv_syn_cnnc] using (nb072_compact_fv_empty_0081 x y H)

theorem nb072_wpp_notmem_0272 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_093 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_093, fv_syn_cnnc] using (nb072_compact_fv_empty_0082 A B R S_cls H)

theorem nb072_wpp_notmem_0273 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_095 x y H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_095, fv_syn_cnnc] using (nb072_compact_fv_empty_0083 x y H)

theorem nb072_compact_envfresh_0021 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TEnvFresh [((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)), ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)), ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb072_alpha_dummy_096 A B R S_cls H) (nb072_alpha_dummy_097 x y H) (nb072_wpp_notmem_0268 A B R S_cls H) (nb072_wpp_notmem_0269 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_092 A B R S_cls H) (nb072_alpha_dummy_094 x y H) (nb072_wpp_notmem_0270 A B R S_cls H) (nb072_wpp_notmem_0271 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_093 A B R S_cls H) (nb072_alpha_dummy_095 x y H) (nb072_wpp_notmem_0272 A B R S_cls H) (nb072_wpp_notmem_0273 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_039 A B R S_cls H) (nb072_alpha_dummy_041 x y H) (nb072_wpp_notmem_0192 A B R S_cls H) (nb072_wpp_notmem_0193 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_038 A B R S_cls H) (nb072_alpha_dummy_040 x y H) (nb072_wpp_notmem_0194 A B R S_cls H) (nb072_wpp_notmem_0195 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_044 A B R S_cls H) (nb072_alpha_dummy_045 x y H) (nb072_wpp_notmem_0196 A B R S_cls H) (nb072_wpp_notmem_0197 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_042 A B R S_cls H) (nb072_alpha_dummy_043 x y H) (nb072_wpp_notmem_0198 A B R S_cls H) (nb072_wpp_notmem_0199 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y (nb072_wpp_notmem_0062 A B R S_cls H) (nb072_wpp_notmem_0063 y) (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x (nb072_wpp_notmem_0064 A B R S_cls H) (nb072_wpp_notmem_0065 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))

noncomputable def nb072_wpp_refl_0017 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TReflOn [((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)), ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)), ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0021 x y A B R S_cls H)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
