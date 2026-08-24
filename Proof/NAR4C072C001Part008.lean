import NAR4C072C001Part007

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

theorem nb072_wpp_notmem_0108 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_063 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_063, fv_syn_c1c] using (nb072_compact_fv_empty_0040 A B R S_cls H)

theorem nb072_compact_fv_empty_0041 (x : Var) (H : Class) : (nb072_alpha_dummy_065 x H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0109 (x : Var) (H : Class) : (nb072_alpha_dummy_065 x H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_065, fv_syn_c1c] using (nb072_compact_fv_empty_0041 x H)

theorem nb072_compact_fv_empty_0042 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_055 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0110 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_055 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_055, fv_syn_c1c] using (nb072_compact_fv_empty_0042 A B R S_cls H)

theorem nb072_compact_fv_empty_0043 (x : Var) (H : Class) : (nb072_alpha_dummy_057 x H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0111 (x : Var) (H : Class) : (nb072_alpha_dummy_057 x H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_057, fv_syn_c1c] using (nb072_compact_fv_empty_0043 x H)

theorem nb072_compact_fv_empty_0044 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_054 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0112 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_054 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_054, fv_syn_c1c] using (nb072_compact_fv_empty_0044 A B R S_cls H)

theorem nb072_compact_fv_empty_0045 (x : Var) (H : Class) : (nb072_alpha_dummy_056 x H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0113 (x : Var) (H : Class) : (nb072_alpha_dummy_056 x H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_056, fv_syn_c1c] using (nb072_compact_fv_empty_0045 x H)

theorem nb072_compact_fv_empty_0046 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_060 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0114 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_060 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_060, fv_syn_c1c] using (nb072_compact_fv_empty_0046 A B R S_cls H)

theorem nb072_compact_fv_empty_0047 (x : Var) (H : Class) : (nb072_alpha_dummy_061 x H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0115 (x : Var) (H : Class) : (nb072_alpha_dummy_061 x H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_061, fv_syn_c1c] using (nb072_compact_fv_empty_0047 x H)

theorem nb072_compact_fv_empty_0048 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_058 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0116 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_058 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_058, fv_syn_c1c] using (nb072_compact_fv_empty_0048 A B R S_cls H)

theorem nb072_compact_fv_empty_0049 (x : Var) (H : Class) : (nb072_alpha_dummy_059 x H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0117 (x : Var) (H : Class) : (nb072_alpha_dummy_059 x H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_059, fv_syn_c1c] using (nb072_compact_fv_empty_0049 x H)

theorem nb072_compact_fv_empty_0050 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_046 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0118 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_046 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_046, fv_syn_c1c] using (nb072_compact_fv_empty_0050 A B R S_cls H)

theorem nb072_compact_fv_empty_0051 (x : Var) (H : Class) : (nb072_alpha_dummy_047 x H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0119 (x : Var) (H : Class) : (nb072_alpha_dummy_047 x H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_047, fv_syn_c1c] using (nb072_compact_fv_empty_0051 x H)

theorem nb072_compact_fv_empty_0052 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_048 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0120 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_048 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_048, fv_syn_c1c] using (nb072_compact_fv_empty_0052 A B R S_cls H)

theorem nb072_compact_fv_empty_0053 (x : Var) (H : Class) : (nb072_alpha_dummy_049 x H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0121 (x : Var) (H : Class) : (nb072_alpha_dummy_049 x H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_049, fv_syn_c1c] using (nb072_compact_fv_empty_0053 x H)

theorem nb072_compact_fv_empty_0054 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_051 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0122 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_051 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_051, fv_syn_c1c] using (nb072_compact_fv_empty_0054 A B R S_cls H)

theorem nb072_compact_fv_empty_0055 (x : Var) (H : Class) : (nb072_alpha_dummy_053 x H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0123 (x : Var) (H : Class) : (nb072_alpha_dummy_053 x H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_053, fv_syn_c1c] using (nb072_compact_fv_empty_0055 x H)

theorem nb072_compact_fv_empty_0056 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_050 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0124 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_050 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_050, fv_syn_c1c] using (nb072_compact_fv_empty_0056 A B R S_cls H)

theorem nb072_compact_fv_empty_0057 (x : Var) (H : Class) : (nb072_alpha_dummy_052 x H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0125 (x : Var) (H : Class) : (nb072_alpha_dummy_052 x H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_052, fv_syn_c1c] using (nb072_compact_fv_empty_0057 x H)

theorem nb072_compact_fv_empty_0058 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_039 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0126 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_039 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_039, fv_syn_c1c] using (nb072_compact_fv_empty_0058 A B R S_cls H)

theorem nb072_compact_fv_empty_0059 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_041 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0127 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_041 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_041, fv_syn_c1c] using (nb072_compact_fv_empty_0059 x y H)

theorem nb072_compact_fv_empty_0060 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_038 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0128 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_038 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_038, fv_syn_c1c] using (nb072_compact_fv_empty_0060 A B R S_cls H)

theorem nb072_compact_fv_empty_0061 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_040 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0129 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_040 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_040, fv_syn_c1c] using (nb072_compact_fv_empty_0061 x y H)

theorem nb072_compact_fv_empty_0062 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_044 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0130 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_044 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_044, fv_syn_c1c] using (nb072_compact_fv_empty_0062 A B R S_cls H)

theorem nb072_compact_fv_empty_0063 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_045 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0131 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_045 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_045, fv_syn_c1c] using (nb072_compact_fv_empty_0063 x y H)

theorem nb072_compact_fv_empty_0064 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_042 A B R S_cls H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0132 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_042 A B R S_cls H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_042, fv_syn_c1c] using (nb072_compact_fv_empty_0064 A B R S_cls H)

theorem nb072_compact_fv_empty_0065 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_043 x y H) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb072_wpp_notmem_0133 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_043 x y H) ∉ ((syn_c1c)).fv := by
  simpa only [nb072_alpha_dummy_043, fv_syn_c1c] using (nb072_compact_fv_empty_0065 x y H)

theorem nb072_compact_envfresh_0011 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TEnvFresh [((nb072_alpha_dummy_070 A B R S_cls H), (nb072_alpha_dummy_073 x H)), ((nb072_alpha_dummy_069 A B R S_cls H), (nb072_alpha_dummy_072 x H)), ((nb072_alpha_dummy_068 A B R S_cls H), (nb072_alpha_dummy_071 x H)), ((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)), ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)), ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)), ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)), ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)), ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)), ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)), ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb072_alpha_dummy_070 A B R S_cls H) (nb072_alpha_dummy_073 x H) (nb072_wpp_notmem_0098 A B R S_cls H) (nb072_wpp_notmem_0099 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_069 A B R S_cls H) (nb072_alpha_dummy_072 x H) (nb072_wpp_notmem_0100 A B R S_cls H) (nb072_wpp_notmem_0101 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_068 A B R S_cls H) (nb072_alpha_dummy_071 x H) (nb072_wpp_notmem_0102 A B R S_cls H) (nb072_wpp_notmem_0103 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_066 A B R S_cls H) (nb072_alpha_dummy_067 x H) (nb072_wpp_notmem_0104 A B R S_cls H) (nb072_wpp_notmem_0105 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_062 A B R S_cls H) (nb072_alpha_dummy_064 x H) (nb072_wpp_notmem_0106 A B R S_cls H) (nb072_wpp_notmem_0107 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_063 A B R S_cls H) (nb072_alpha_dummy_065 x H) (nb072_wpp_notmem_0108 A B R S_cls H) (nb072_wpp_notmem_0109 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_055 A B R S_cls H) (nb072_alpha_dummy_057 x H) (nb072_wpp_notmem_0110 A B R S_cls H) (nb072_wpp_notmem_0111 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_054 A B R S_cls H) (nb072_alpha_dummy_056 x H) (nb072_wpp_notmem_0112 A B R S_cls H) (nb072_wpp_notmem_0113 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_060 A B R S_cls H) (nb072_alpha_dummy_061 x H) (nb072_wpp_notmem_0114 A B R S_cls H) (nb072_wpp_notmem_0115 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_058 A B R S_cls H) (nb072_alpha_dummy_059 x H) (nb072_wpp_notmem_0116 A B R S_cls H) (nb072_wpp_notmem_0117 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_046 A B R S_cls H) (nb072_alpha_dummy_047 x H) (nb072_wpp_notmem_0118 A B R S_cls H) (nb072_wpp_notmem_0119 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_048 A B R S_cls H) (nb072_alpha_dummy_049 x H) (nb072_wpp_notmem_0120 A B R S_cls H) (nb072_wpp_notmem_0121 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_051 A B R S_cls H) (nb072_alpha_dummy_053 x H) (nb072_wpp_notmem_0122 A B R S_cls H) (nb072_wpp_notmem_0123 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_050 A B R S_cls H) (nb072_alpha_dummy_052 x H) (nb072_wpp_notmem_0124 A B R S_cls H) (nb072_wpp_notmem_0125 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_039 A B R S_cls H) (nb072_alpha_dummy_041 x y H) (nb072_wpp_notmem_0126 A B R S_cls H) (nb072_wpp_notmem_0127 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_038 A B R S_cls H) (nb072_alpha_dummy_040 x y H) (nb072_wpp_notmem_0128 A B R S_cls H) (nb072_wpp_notmem_0129 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_044 A B R S_cls H) (nb072_alpha_dummy_045 x y H) (nb072_wpp_notmem_0130 A B R S_cls H) (nb072_wpp_notmem_0131 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_042 A B R S_cls H) (nb072_alpha_dummy_043 x y H) (nb072_wpp_notmem_0132 A B R S_cls H) (nb072_wpp_notmem_0133 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y (nb072_wpp_notmem_0020 A B R S_cls H) (nb072_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x (nb072_wpp_notmem_0022 A B R S_cls H) (nb072_wpp_notmem_0023 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb072_wpp_refl_0008 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TReflOn [((nb072_alpha_dummy_070 A B R S_cls H), (nb072_alpha_dummy_073 x H)), ((nb072_alpha_dummy_069 A B R S_cls H), (nb072_alpha_dummy_072 x H)), ((nb072_alpha_dummy_068 A B R S_cls H), (nb072_alpha_dummy_071 x H)), ((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)), ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)), ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)), ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)), ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)), ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)), ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)), ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0011 x y A B R S_cls H)

theorem nb072_wpp_notmem_0134 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_070 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_070, fv_syn_c0] using (nb072_compact_fv_empty_0030 A B R S_cls H)

theorem nb072_wpp_notmem_0135 (x : Var) (H : Class) : (nb072_alpha_dummy_073 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_073, fv_syn_c0] using (nb072_compact_fv_empty_0031 x H)

theorem nb072_wpp_notmem_0136 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_069 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_069, fv_syn_c0] using (nb072_compact_fv_empty_0032 A B R S_cls H)

theorem nb072_wpp_notmem_0137 (x : Var) (H : Class) : (nb072_alpha_dummy_072 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_072, fv_syn_c0] using (nb072_compact_fv_empty_0033 x H)

theorem nb072_wpp_notmem_0138 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_068 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_068, fv_syn_c0] using (nb072_compact_fv_empty_0034 A B R S_cls H)

theorem nb072_wpp_notmem_0139 (x : Var) (H : Class) : (nb072_alpha_dummy_071 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_071, fv_syn_c0] using (nb072_compact_fv_empty_0035 x H)

theorem nb072_wpp_notmem_0140 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_066 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_066, fv_syn_c0] using (nb072_compact_fv_empty_0036 A B R S_cls H)

theorem nb072_wpp_notmem_0141 (x : Var) (H : Class) : (nb072_alpha_dummy_067 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_067, fv_syn_c0] using (nb072_compact_fv_empty_0037 x H)

theorem nb072_wpp_notmem_0142 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_062 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_062, fv_syn_c0] using (nb072_compact_fv_empty_0038 A B R S_cls H)

theorem nb072_wpp_notmem_0143 (x : Var) (H : Class) : (nb072_alpha_dummy_064 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_064, fv_syn_c0] using (nb072_compact_fv_empty_0039 x H)

theorem nb072_wpp_notmem_0144 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_063 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_063, fv_syn_c0] using (nb072_compact_fv_empty_0040 A B R S_cls H)

theorem nb072_wpp_notmem_0145 (x : Var) (H : Class) : (nb072_alpha_dummy_065 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_065, fv_syn_c0] using (nb072_compact_fv_empty_0041 x H)

theorem nb072_wpp_notmem_0146 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_055 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_055, fv_syn_c0] using (nb072_compact_fv_empty_0042 A B R S_cls H)

theorem nb072_wpp_notmem_0147 (x : Var) (H : Class) : (nb072_alpha_dummy_057 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_057, fv_syn_c0] using (nb072_compact_fv_empty_0043 x H)

theorem nb072_wpp_notmem_0148 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_054 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_054, fv_syn_c0] using (nb072_compact_fv_empty_0044 A B R S_cls H)

theorem nb072_wpp_notmem_0149 (x : Var) (H : Class) : (nb072_alpha_dummy_056 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_056, fv_syn_c0] using (nb072_compact_fv_empty_0045 x H)

theorem nb072_wpp_notmem_0150 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_060 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_060, fv_syn_c0] using (nb072_compact_fv_empty_0046 A B R S_cls H)

theorem nb072_wpp_notmem_0151 (x : Var) (H : Class) : (nb072_alpha_dummy_061 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_061, fv_syn_c0] using (nb072_compact_fv_empty_0047 x H)

theorem nb072_wpp_notmem_0152 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_058 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_058, fv_syn_c0] using (nb072_compact_fv_empty_0048 A B R S_cls H)

theorem nb072_wpp_notmem_0153 (x : Var) (H : Class) : (nb072_alpha_dummy_059 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_059, fv_syn_c0] using (nb072_compact_fv_empty_0049 x H)

theorem nb072_wpp_notmem_0154 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_046 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_046, fv_syn_c0] using (nb072_compact_fv_empty_0050 A B R S_cls H)

theorem nb072_wpp_notmem_0155 (x : Var) (H : Class) : (nb072_alpha_dummy_047 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_047, fv_syn_c0] using (nb072_compact_fv_empty_0051 x H)

theorem nb072_wpp_notmem_0156 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_048 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_048, fv_syn_c0] using (nb072_compact_fv_empty_0052 A B R S_cls H)

theorem nb072_wpp_notmem_0157 (x : Var) (H : Class) : (nb072_alpha_dummy_049 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_049, fv_syn_c0] using (nb072_compact_fv_empty_0053 x H)

theorem nb072_wpp_notmem_0158 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_051 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_051, fv_syn_c0] using (nb072_compact_fv_empty_0054 A B R S_cls H)

theorem nb072_wpp_notmem_0159 (x : Var) (H : Class) : (nb072_alpha_dummy_053 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_053, fv_syn_c0] using (nb072_compact_fv_empty_0055 x H)

theorem nb072_wpp_notmem_0160 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_050 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_050, fv_syn_c0] using (nb072_compact_fv_empty_0056 A B R S_cls H)

theorem nb072_wpp_notmem_0161 (x : Var) (H : Class) : (nb072_alpha_dummy_052 x H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_052, fv_syn_c0] using (nb072_compact_fv_empty_0057 x H)

theorem nb072_wpp_notmem_0162 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_039 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_039, fv_syn_c0] using (nb072_compact_fv_empty_0058 A B R S_cls H)

theorem nb072_wpp_notmem_0163 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_041 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_041, fv_syn_c0] using (nb072_compact_fv_empty_0059 x y H)

theorem nb072_wpp_notmem_0164 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_038 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_038, fv_syn_c0] using (nb072_compact_fv_empty_0060 A B R S_cls H)

theorem nb072_wpp_notmem_0165 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_040 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_040, fv_syn_c0] using (nb072_compact_fv_empty_0061 x y H)

theorem nb072_wpp_notmem_0166 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_044 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_044, fv_syn_c0] using (nb072_compact_fv_empty_0062 A B R S_cls H)

theorem nb072_wpp_notmem_0167 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_045 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_045, fv_syn_c0] using (nb072_compact_fv_empty_0063 x y H)

theorem nb072_wpp_notmem_0168 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_042 A B R S_cls H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_042, fv_syn_c0] using (nb072_compact_fv_empty_0064 A B R S_cls H)

theorem nb072_wpp_notmem_0169 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_043 x y H) ∉ ((syn_c0)).fv := by
  simpa only [nb072_alpha_dummy_043, fv_syn_c0] using (nb072_compact_fv_empty_0065 x y H)

theorem nb072_compact_envfresh_0012 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TEnvFresh [((nb072_alpha_dummy_070 A B R S_cls H), (nb072_alpha_dummy_073 x H)), ((nb072_alpha_dummy_069 A B R S_cls H), (nb072_alpha_dummy_072 x H)), ((nb072_alpha_dummy_068 A B R S_cls H), (nb072_alpha_dummy_071 x H)), ((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)), ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)), ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)), ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)), ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)), ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)), ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)), ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb072_alpha_dummy_070 A B R S_cls H) (nb072_alpha_dummy_073 x H) (nb072_wpp_notmem_0134 A B R S_cls H) (nb072_wpp_notmem_0135 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_069 A B R S_cls H) (nb072_alpha_dummy_072 x H) (nb072_wpp_notmem_0136 A B R S_cls H) (nb072_wpp_notmem_0137 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_068 A B R S_cls H) (nb072_alpha_dummy_071 x H) (nb072_wpp_notmem_0138 A B R S_cls H) (nb072_wpp_notmem_0139 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_066 A B R S_cls H) (nb072_alpha_dummy_067 x H) (nb072_wpp_notmem_0140 A B R S_cls H) (nb072_wpp_notmem_0141 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_062 A B R S_cls H) (nb072_alpha_dummy_064 x H) (nb072_wpp_notmem_0142 A B R S_cls H) (nb072_wpp_notmem_0143 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_063 A B R S_cls H) (nb072_alpha_dummy_065 x H) (nb072_wpp_notmem_0144 A B R S_cls H) (nb072_wpp_notmem_0145 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_055 A B R S_cls H) (nb072_alpha_dummy_057 x H) (nb072_wpp_notmem_0146 A B R S_cls H) (nb072_wpp_notmem_0147 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_054 A B R S_cls H) (nb072_alpha_dummy_056 x H) (nb072_wpp_notmem_0148 A B R S_cls H) (nb072_wpp_notmem_0149 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_060 A B R S_cls H) (nb072_alpha_dummy_061 x H) (nb072_wpp_notmem_0150 A B R S_cls H) (nb072_wpp_notmem_0151 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_058 A B R S_cls H) (nb072_alpha_dummy_059 x H) (nb072_wpp_notmem_0152 A B R S_cls H) (nb072_wpp_notmem_0153 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_046 A B R S_cls H) (nb072_alpha_dummy_047 x H) (nb072_wpp_notmem_0154 A B R S_cls H) (nb072_wpp_notmem_0155 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_048 A B R S_cls H) (nb072_alpha_dummy_049 x H) (nb072_wpp_notmem_0156 A B R S_cls H) (nb072_wpp_notmem_0157 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_051 A B R S_cls H) (nb072_alpha_dummy_053 x H) (nb072_wpp_notmem_0158 A B R S_cls H) (nb072_wpp_notmem_0159 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_050 A B R S_cls H) (nb072_alpha_dummy_052 x H) (nb072_wpp_notmem_0160 A B R S_cls H) (nb072_wpp_notmem_0161 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_039 A B R S_cls H) (nb072_alpha_dummy_041 x y H) (nb072_wpp_notmem_0162 A B R S_cls H) (nb072_wpp_notmem_0163 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_038 A B R S_cls H) (nb072_alpha_dummy_040 x y H) (nb072_wpp_notmem_0164 A B R S_cls H) (nb072_wpp_notmem_0165 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_044 A B R S_cls H) (nb072_alpha_dummy_045 x y H) (nb072_wpp_notmem_0166 A B R S_cls H) (nb072_wpp_notmem_0167 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_042 A B R S_cls H) (nb072_alpha_dummy_043 x y H) (nb072_wpp_notmem_0168 A B R S_cls H) (nb072_wpp_notmem_0169 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y (nb072_wpp_notmem_0044 A B R S_cls H) (nb072_wpp_notmem_0045 y) (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x (nb072_wpp_notmem_0046 A B R S_cls H) (nb072_wpp_notmem_0047 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb072_wpp_refl_0009 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TReflOn [((nb072_alpha_dummy_070 A B R S_cls H), (nb072_alpha_dummy_073 x H)), ((nb072_alpha_dummy_069 A B R S_cls H), (nb072_alpha_dummy_072 x H)), ((nb072_alpha_dummy_068 A B R S_cls H), (nb072_alpha_dummy_071 x H)), ((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)), ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)), ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)), ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)), ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)), ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)), ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)), ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0012 x y A B R S_cls H)

theorem nb072_wpp_notmem_0170 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_066 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_066, fv_syn_cnnc] using (nb072_compact_fv_empty_0036 A B R S_cls H)

theorem nb072_wpp_notmem_0171 (x : Var) (H : Class) : (nb072_alpha_dummy_067 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_067, fv_syn_cnnc] using (nb072_compact_fv_empty_0037 x H)

theorem nb072_wpp_notmem_0172 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_062 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_062, fv_syn_cnnc] using (nb072_compact_fv_empty_0038 A B R S_cls H)

theorem nb072_wpp_notmem_0173 (x : Var) (H : Class) : (nb072_alpha_dummy_064 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_064, fv_syn_cnnc] using (nb072_compact_fv_empty_0039 x H)

theorem nb072_wpp_notmem_0174 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_063 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_063, fv_syn_cnnc] using (nb072_compact_fv_empty_0040 A B R S_cls H)

theorem nb072_wpp_notmem_0175 (x : Var) (H : Class) : (nb072_alpha_dummy_065 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_065, fv_syn_cnnc] using (nb072_compact_fv_empty_0041 x H)

theorem nb072_wpp_notmem_0176 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_055 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_055, fv_syn_cnnc] using (nb072_compact_fv_empty_0042 A B R S_cls H)

theorem nb072_wpp_notmem_0177 (x : Var) (H : Class) : (nb072_alpha_dummy_057 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_057, fv_syn_cnnc] using (nb072_compact_fv_empty_0043 x H)

theorem nb072_wpp_notmem_0178 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_054 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_054, fv_syn_cnnc] using (nb072_compact_fv_empty_0044 A B R S_cls H)

theorem nb072_wpp_notmem_0179 (x : Var) (H : Class) : (nb072_alpha_dummy_056 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_056, fv_syn_cnnc] using (nb072_compact_fv_empty_0045 x H)

theorem nb072_wpp_notmem_0180 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_060 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_060, fv_syn_cnnc] using (nb072_compact_fv_empty_0046 A B R S_cls H)

theorem nb072_wpp_notmem_0181 (x : Var) (H : Class) : (nb072_alpha_dummy_061 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_061, fv_syn_cnnc] using (nb072_compact_fv_empty_0047 x H)

theorem nb072_wpp_notmem_0182 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_058 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_058, fv_syn_cnnc] using (nb072_compact_fv_empty_0048 A B R S_cls H)

theorem nb072_wpp_notmem_0183 (x : Var) (H : Class) : (nb072_alpha_dummy_059 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_059, fv_syn_cnnc] using (nb072_compact_fv_empty_0049 x H)

theorem nb072_wpp_notmem_0184 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_046 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_046, fv_syn_cnnc] using (nb072_compact_fv_empty_0050 A B R S_cls H)

theorem nb072_wpp_notmem_0185 (x : Var) (H : Class) : (nb072_alpha_dummy_047 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_047, fv_syn_cnnc] using (nb072_compact_fv_empty_0051 x H)

theorem nb072_wpp_notmem_0186 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_048 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_048, fv_syn_cnnc] using (nb072_compact_fv_empty_0052 A B R S_cls H)

theorem nb072_wpp_notmem_0187 (x : Var) (H : Class) : (nb072_alpha_dummy_049 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_049, fv_syn_cnnc] using (nb072_compact_fv_empty_0053 x H)

theorem nb072_wpp_notmem_0188 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_051 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_051, fv_syn_cnnc] using (nb072_compact_fv_empty_0054 A B R S_cls H)

theorem nb072_wpp_notmem_0189 (x : Var) (H : Class) : (nb072_alpha_dummy_053 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_053, fv_syn_cnnc] using (nb072_compact_fv_empty_0055 x H)

theorem nb072_wpp_notmem_0190 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_050 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_050, fv_syn_cnnc] using (nb072_compact_fv_empty_0056 A B R S_cls H)

theorem nb072_wpp_notmem_0191 (x : Var) (H : Class) : (nb072_alpha_dummy_052 x H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_052, fv_syn_cnnc] using (nb072_compact_fv_empty_0057 x H)

theorem nb072_wpp_notmem_0192 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_039 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_039, fv_syn_cnnc] using (nb072_compact_fv_empty_0058 A B R S_cls H)

theorem nb072_wpp_notmem_0193 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_041 x y H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_041, fv_syn_cnnc] using (nb072_compact_fv_empty_0059 x y H)

theorem nb072_wpp_notmem_0194 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_038 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_038, fv_syn_cnnc] using (nb072_compact_fv_empty_0060 A B R S_cls H)

theorem nb072_wpp_notmem_0195 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_040 x y H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_040, fv_syn_cnnc] using (nb072_compact_fv_empty_0061 x y H)

theorem nb072_wpp_notmem_0196 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_044 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_044, fv_syn_cnnc] using (nb072_compact_fv_empty_0062 A B R S_cls H)

theorem nb072_wpp_notmem_0197 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_045 x y H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_045, fv_syn_cnnc] using (nb072_compact_fv_empty_0063 x y H)

theorem nb072_wpp_notmem_0198 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_042 A B R S_cls H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_042, fv_syn_cnnc] using (nb072_compact_fv_empty_0064 A B R S_cls H)

theorem nb072_wpp_notmem_0199 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_043 x y H) ∉ ((syn_cnnc)).fv := by
  simpa only [nb072_alpha_dummy_043, fv_syn_cnnc] using (nb072_compact_fv_empty_0065 x y H)

theorem nb072_compact_envfresh_0013 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TEnvFresh [((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)), ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)), ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)), ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)), ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)), ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)), ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)), ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb072_alpha_dummy_066 A B R S_cls H) (nb072_alpha_dummy_067 x H) (nb072_wpp_notmem_0170 A B R S_cls H) (nb072_wpp_notmem_0171 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_062 A B R S_cls H) (nb072_alpha_dummy_064 x H) (nb072_wpp_notmem_0172 A B R S_cls H) (nb072_wpp_notmem_0173 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_063 A B R S_cls H) (nb072_alpha_dummy_065 x H) (nb072_wpp_notmem_0174 A B R S_cls H) (nb072_wpp_notmem_0175 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_055 A B R S_cls H) (nb072_alpha_dummy_057 x H) (nb072_wpp_notmem_0176 A B R S_cls H) (nb072_wpp_notmem_0177 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_054 A B R S_cls H) (nb072_alpha_dummy_056 x H) (nb072_wpp_notmem_0178 A B R S_cls H) (nb072_wpp_notmem_0179 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_060 A B R S_cls H) (nb072_alpha_dummy_061 x H) (nb072_wpp_notmem_0180 A B R S_cls H) (nb072_wpp_notmem_0181 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_058 A B R S_cls H) (nb072_alpha_dummy_059 x H) (nb072_wpp_notmem_0182 A B R S_cls H) (nb072_wpp_notmem_0183 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_046 A B R S_cls H) (nb072_alpha_dummy_047 x H) (nb072_wpp_notmem_0184 A B R S_cls H) (nb072_wpp_notmem_0185 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_048 A B R S_cls H) (nb072_alpha_dummy_049 x H) (nb072_wpp_notmem_0186 A B R S_cls H) (nb072_wpp_notmem_0187 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_051 A B R S_cls H) (nb072_alpha_dummy_053 x H) (nb072_wpp_notmem_0188 A B R S_cls H) (nb072_wpp_notmem_0189 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_050 A B R S_cls H) (nb072_alpha_dummy_052 x H) (nb072_wpp_notmem_0190 A B R S_cls H) (nb072_wpp_notmem_0191 x H) (TEnvFresh.consFresh (nb072_alpha_dummy_039 A B R S_cls H) (nb072_alpha_dummy_041 x y H) (nb072_wpp_notmem_0192 A B R S_cls H) (nb072_wpp_notmem_0193 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_038 A B R S_cls H) (nb072_alpha_dummy_040 x y H) (nb072_wpp_notmem_0194 A B R S_cls H) (nb072_wpp_notmem_0195 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_044 A B R S_cls H) (nb072_alpha_dummy_045 x y H) (nb072_wpp_notmem_0196 A B R S_cls H) (nb072_wpp_notmem_0197 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_042 A B R S_cls H) (nb072_alpha_dummy_043 x y H) (nb072_wpp_notmem_0198 A B R S_cls H) (nb072_wpp_notmem_0199 x y H) (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y (nb072_wpp_notmem_0062 A B R S_cls H) (nb072_wpp_notmem_0063 y) (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x (nb072_wpp_notmem_0064 A B R S_cls H) (nb072_wpp_notmem_0065 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb072_wpp_refl_0010 (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : TReflOn [((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)), ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)), ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)), ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)), ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)), ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)), ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)), ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0013 x y A B R S_cls H)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
