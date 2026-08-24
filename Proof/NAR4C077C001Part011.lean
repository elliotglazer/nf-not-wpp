import NAR4C077C001Part010

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

noncomputable def nb077_wpp_refl_0006 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)), ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)), ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)), ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0006 x F I)

theorem nb077_wpp_notmem_0118 (F : Class) (I : Class) : (nb077_alpha_dummy_053 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_053, fv_syn_cnnc] using (nb077_compact_fv_empty_0038 F I)

theorem nb077_wpp_notmem_0119 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_054 x F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_054, fv_syn_cnnc] using (nb077_compact_fv_empty_0039 x F I)

theorem nb077_wpp_notmem_0120 (F : Class) (I : Class) : (nb077_alpha_dummy_051 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_051, fv_syn_cnnc] using (nb077_compact_fv_empty_0040 F I)

theorem nb077_wpp_notmem_0121 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_052 x F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_052, fv_syn_cnnc] using (nb077_compact_fv_empty_0041 x F I)

theorem nb077_wpp_notmem_0122 (F : Class) (I : Class) : (nb077_alpha_dummy_049 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_049, fv_syn_cnnc] using (nb077_compact_fv_empty_0042 F I)

theorem nb077_wpp_notmem_0123 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_050 x F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_050, fv_syn_cnnc] using (nb077_compact_fv_empty_0043 x F I)

theorem nb077_compact_envfresh_0007 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_031 F I) (nb077_alpha_dummy_032 x F I) (nb077_wpp_notmem_0078 F I) (nb077_wpp_notmem_0079 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_027 F I) (nb077_alpha_dummy_029 x F I) (nb077_wpp_notmem_0080 F I) (nb077_wpp_notmem_0081 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_028 F I) (nb077_alpha_dummy_030 x F I) (nb077_wpp_notmem_0082 F I) (nb077_wpp_notmem_0083 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_053 F I) (nb077_alpha_dummy_054 x F I) (nb077_wpp_notmem_0118 F I) (nb077_wpp_notmem_0119 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_051 F I) (nb077_alpha_dummy_052 x F I) (nb077_wpp_notmem_0120 F I) (nb077_wpp_notmem_0121 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_020 F I) (nb077_alpha_dummy_022 x F I) (nb077_wpp_notmem_0084 F I) (nb077_wpp_notmem_0085 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_019 F I) (nb077_alpha_dummy_021 x F I) (nb077_wpp_notmem_0086 F I) (nb077_wpp_notmem_0087 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_049 F I) (nb077_alpha_dummy_050 x F I) (nb077_wpp_notmem_0122 F I) (nb077_wpp_notmem_0123 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_023 F I) (nb077_alpha_dummy_024 x F I) (nb077_wpp_notmem_0090 F I) (nb077_wpp_notmem_0091 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0092 F I) (nb077_wpp_notmem_0093 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0094 F I) (nb077_wpp_notmem_0095 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0096 F I) (nb077_wpp_notmem_0097 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0098 F I) (nb077_wpp_notmem_0099 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0100 F I) (nb077_wpp_notmem_0101 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0102 F I) (nb077_wpp_notmem_0103 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0104 F I) (nb077_wpp_notmem_0105 x F I) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb077_wpp_refl_0007 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0007 x F I)

theorem nb077_wpp_notmem_0124 (F : Class) (I : Class) : (nb077_alpha_dummy_051 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_051, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0040 F I)

theorem nb077_wpp_notmem_0125 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_052 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_052, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0041 x F I)

theorem nb077_wpp_notmem_0126 (F : Class) (I : Class) : (nb077_alpha_dummy_020 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_020, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0022 F I)

theorem nb077_wpp_notmem_0127 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_022 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_022, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0023 x F I)

theorem nb077_wpp_notmem_0128 (F : Class) (I : Class) : (nb077_alpha_dummy_019 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_019, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0024 F I)

theorem nb077_wpp_notmem_0129 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_021 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_021, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0025 x F I)

theorem nb077_wpp_notmem_0130 (F : Class) (I : Class) : (nb077_alpha_dummy_049 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_049, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0042 F I)

theorem nb077_wpp_notmem_0131 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_050 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_050, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0043 x F I)

theorem nb077_wpp_notmem_0132 (F : Class) (I : Class) : (nb077_alpha_dummy_023 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_023, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0028 F I)

theorem nb077_wpp_notmem_0133 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_024 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_024, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0029 x F I)

theorem nb077_wpp_notmem_0134 (F : Class) (I : Class) : (nb077_alpha_dummy_016 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_016, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0030 F I)

theorem nb077_wpp_notmem_0135 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_018 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_018, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0031 x F I)

theorem nb077_wpp_notmem_0136 (F : Class) (I : Class) : (nb077_alpha_dummy_015 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_015, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0032 F I)

theorem nb077_wpp_notmem_0137 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_017 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_017, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0033 x F I)

theorem nb077_wpp_notmem_0138 (F : Class) (I : Class) : (nb077_alpha_dummy_013 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_013, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0034 F I)

theorem nb077_wpp_notmem_0139 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_014 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_014, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0035 x F I)

theorem nb077_wpp_notmem_0140 (F : Class) (I : Class) : (nb077_alpha_dummy_011 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_011, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0036 F I)

theorem nb077_wpp_notmem_0141 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_012 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_012, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0037 x F I)

theorem nb077_wpp_notmem_0142 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0004 F I)

theorem nb077_wpp_notmem_0143 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0005 x F I)

theorem nb077_wpp_notmem_0144 (F : Class) (I : Class) : (nb077_alpha_dummy_004 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0006 F I)

theorem nb077_wpp_notmem_0145 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_006 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0007 x F I)

theorem nb077_wpp_notmem_0146 (F : Class) (I : Class) : (nb077_alpha_dummy_003 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0008 F I)

theorem nb077_wpp_notmem_0147 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_005 x F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0009 x F I)

theorem nb077_compact_envfresh_0008 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_051 F I) (nb077_alpha_dummy_052 x F I) (nb077_wpp_notmem_0124 F I) (nb077_wpp_notmem_0125 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_020 F I) (nb077_alpha_dummy_022 x F I) (nb077_wpp_notmem_0126 F I) (nb077_wpp_notmem_0127 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_019 F I) (nb077_alpha_dummy_021 x F I) (nb077_wpp_notmem_0128 F I) (nb077_wpp_notmem_0129 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_049 F I) (nb077_alpha_dummy_050 x F I) (nb077_wpp_notmem_0130 F I) (nb077_wpp_notmem_0131 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_023 F I) (nb077_alpha_dummy_024 x F I) (nb077_wpp_notmem_0132 F I) (nb077_wpp_notmem_0133 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0134 F I) (nb077_wpp_notmem_0135 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0136 F I) (nb077_wpp_notmem_0137 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0138 F I) (nb077_wpp_notmem_0139 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0140 F I) (nb077_wpp_notmem_0141 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0142 F I) (nb077_wpp_notmem_0143 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0144 F I) (nb077_wpp_notmem_0145 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0146 F I) (nb077_wpp_notmem_0147 x F I) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))

noncomputable def nb077_wpp_refl_0008 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0008 x F I)

noncomputable def nb077_split_alpha_0001 (x : Var) (F : Class) (I : Class) : TAlphaWff [((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_051 F I)) (syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))) (Wff.neg (Wff.classMem (Class.cv (nb077_alpha_dummy_051 F I)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_052 x F I)) (syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))) (Wff.neg (Wff.classMem (Class.cv (nb077_alpha_dummy_052 x F I)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0017 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0016 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0017 x F I) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0046 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0047 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0044 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0045 x F I) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0020 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0021 x F I) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0020 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0021 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0018 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0019 x F I) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)), ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)), ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)), ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c) (nb077_wpp_refl_0005 x F I))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0024 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0025 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0022 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0023 x F I) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0028 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0029 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0026 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0027 x F I) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0024 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0025 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0022 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0023 x F I) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0028 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0029 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0026 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0027 x F I) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)), ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)), ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)), ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0) (nb077_wpp_refl_0006 x F I))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0032 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0033 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0030 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0031 x F I) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0032 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0033 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0030 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0031 x F I) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0036 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0037 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0034 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0035 x F I) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0036 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0037 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0034 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0035 x F I) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0018 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0019 x F I) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0007 x F I))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0018 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0019 x F I) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0018 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0019 x F I) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0007 x F I)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0017 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0016 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0017 x F I) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0046 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0047 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0044 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0045 x F I) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0020 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0021 x F I) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0020 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0021 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0018 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0019 x F I) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)), ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)), ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)), ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c) (nb077_wpp_refl_0005 x F I))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0024 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0025 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0022 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0023 x F I) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0028 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0029 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0026 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0027 x F I) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0024 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0025 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0022 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0023 x F I) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0028 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0029 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0026 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0027 x F I) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)), ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)), ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)), ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0) (nb077_wpp_refl_0006 x F I))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0032 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0033 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0030 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0031 x F I) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0032 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0033 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0030 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0031 x F I) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0036 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0037 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0034 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0035 x F I) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0036 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0037 x F I) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0034 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0035 x F I) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0018 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0019 x F I) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0007 x F I))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0018 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0019 x F I) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0018 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0019 x F I) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0007 x F I)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_ccompl (syn_csn (syn_c0c))) (nb077_wpp_refl_0008 x F I)))))

theorem nb077_compact_fv_empty_0044 (F : Class) (I : Class) : (nb077_alpha_dummy_083 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0148 (F : Class) (I : Class) : (nb077_alpha_dummy_083 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_083, fv_syn_c1c] using (nb077_compact_fv_empty_0044 F I)

theorem nb077_compact_fv_empty_0045 (x : Var) : (nb077_alpha_dummy_086 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0149 (x : Var) : (nb077_alpha_dummy_086 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_086, fv_syn_c1c] using (nb077_compact_fv_empty_0045 x)

theorem nb077_compact_fv_empty_0046 (F : Class) (I : Class) : (nb077_alpha_dummy_082 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0150 (F : Class) (I : Class) : (nb077_alpha_dummy_082 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_082, fv_syn_c1c] using (nb077_compact_fv_empty_0046 F I)

theorem nb077_compact_fv_empty_0047 (x : Var) : (nb077_alpha_dummy_085 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0151 (x : Var) : (nb077_alpha_dummy_085 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_085, fv_syn_c1c] using (nb077_compact_fv_empty_0047 x)

theorem nb077_compact_fv_empty_0048 (F : Class) (I : Class) : (nb077_alpha_dummy_081 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0152 (F : Class) (I : Class) : (nb077_alpha_dummy_081 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_081, fv_syn_c1c] using (nb077_compact_fv_empty_0048 F I)

theorem nb077_compact_fv_empty_0049 (x : Var) : (nb077_alpha_dummy_084 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0153 (x : Var) : (nb077_alpha_dummy_084 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_084, fv_syn_c1c] using (nb077_compact_fv_empty_0049 x)

theorem nb077_compact_fv_empty_0050 (F : Class) (I : Class) : (nb077_alpha_dummy_079 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0154 (F : Class) (I : Class) : (nb077_alpha_dummy_079 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_079, fv_syn_c1c] using (nb077_compact_fv_empty_0050 F I)

theorem nb077_compact_fv_empty_0051 (x : Var) : (nb077_alpha_dummy_080 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0155 (x : Var) : (nb077_alpha_dummy_080 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_080, fv_syn_c1c] using (nb077_compact_fv_empty_0051 x)

theorem nb077_compact_fv_empty_0052 (F : Class) (I : Class) : (nb077_alpha_dummy_075 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0156 (F : Class) (I : Class) : (nb077_alpha_dummy_075 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_075, fv_syn_c1c] using (nb077_compact_fv_empty_0052 F I)

theorem nb077_compact_fv_empty_0053 (x : Var) : (nb077_alpha_dummy_077 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0157 (x : Var) : (nb077_alpha_dummy_077 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_077, fv_syn_c1c] using (nb077_compact_fv_empty_0053 x)

theorem nb077_compact_fv_empty_0054 (F : Class) (I : Class) : (nb077_alpha_dummy_076 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0158 (F : Class) (I : Class) : (nb077_alpha_dummy_076 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_076, fv_syn_c1c] using (nb077_compact_fv_empty_0054 F I)

theorem nb077_compact_fv_empty_0055 (x : Var) : (nb077_alpha_dummy_078 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0159 (x : Var) : (nb077_alpha_dummy_078 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_078, fv_syn_c1c] using (nb077_compact_fv_empty_0055 x)

theorem nb077_compact_fv_empty_0056 (F : Class) (I : Class) : (nb077_alpha_dummy_068 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0160 (F : Class) (I : Class) : (nb077_alpha_dummy_068 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_068, fv_syn_c1c] using (nb077_compact_fv_empty_0056 F I)

theorem nb077_compact_fv_empty_0057 (x : Var) : (nb077_alpha_dummy_070 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0161 (x : Var) : (nb077_alpha_dummy_070 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_070, fv_syn_c1c] using (nb077_compact_fv_empty_0057 x)

theorem nb077_compact_fv_empty_0058 (F : Class) (I : Class) : (nb077_alpha_dummy_067 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0162 (F : Class) (I : Class) : (nb077_alpha_dummy_067 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_067, fv_syn_c1c] using (nb077_compact_fv_empty_0058 F I)

theorem nb077_compact_fv_empty_0059 (x : Var) : (nb077_alpha_dummy_069 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0163 (x : Var) : (nb077_alpha_dummy_069 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_069, fv_syn_c1c] using (nb077_compact_fv_empty_0059 x)

theorem nb077_compact_fv_empty_0060 (F : Class) (I : Class) : (nb077_alpha_dummy_073 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0164 (F : Class) (I : Class) : (nb077_alpha_dummy_073 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_073, fv_syn_c1c] using (nb077_compact_fv_empty_0060 F I)

theorem nb077_compact_fv_empty_0061 (x : Var) : (nb077_alpha_dummy_074 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0165 (x : Var) : (nb077_alpha_dummy_074 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_074, fv_syn_c1c] using (nb077_compact_fv_empty_0061 x)

theorem nb077_compact_fv_empty_0062 (F : Class) (I : Class) : (nb077_alpha_dummy_071 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0166 (F : Class) (I : Class) : (nb077_alpha_dummy_071 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_071, fv_syn_c1c] using (nb077_compact_fv_empty_0062 F I)

theorem nb077_compact_fv_empty_0063 (x : Var) : (nb077_alpha_dummy_072 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0167 (x : Var) : (nb077_alpha_dummy_072 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_072, fv_syn_c1c] using (nb077_compact_fv_empty_0063 x)

theorem nb077_compact_fv_empty_0064 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0168 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_060, fv_syn_c1c] using (nb077_compact_fv_empty_0064 F I)

theorem nb077_compact_fv_empty_0065 (x : Var) : (nb077_alpha_dummy_063 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0169 (x : Var) : (nb077_alpha_dummy_063 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_063, fv_syn_c1c] using (nb077_compact_fv_empty_0065 x)

theorem nb077_compact_fv_empty_0066 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0170 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_059, fv_syn_c1c] using (nb077_compact_fv_empty_0066 F I)

theorem nb077_compact_fv_empty_0067 (x : Var) : (nb077_alpha_dummy_062 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0171 (x : Var) : (nb077_alpha_dummy_062 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_062, fv_syn_c1c] using (nb077_compact_fv_empty_0067 x)

theorem nb077_compact_fv_empty_0068 (F : Class) (I : Class) : (nb077_alpha_dummy_065 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0172 (F : Class) (I : Class) : (nb077_alpha_dummy_065 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_065, fv_syn_c1c] using (nb077_compact_fv_empty_0068 F I)

theorem nb077_compact_fv_empty_0069 (x : Var) : (nb077_alpha_dummy_066 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0173 (x : Var) : (nb077_alpha_dummy_066 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_066, fv_syn_c1c] using (nb077_compact_fv_empty_0069 x)

theorem nb077_compact_fv_empty_0070 (F : Class) (I : Class) : (nb077_alpha_dummy_057 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0174 (F : Class) (I : Class) : (nb077_alpha_dummy_057 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_057, fv_syn_c1c] using (nb077_compact_fv_empty_0070 F I)

theorem nb077_compact_fv_empty_0071 (x : Var) (F : Class) : (nb077_alpha_dummy_058 x F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0175 (x : Var) (F : Class) : (nb077_alpha_dummy_058 x F) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_058, fv_syn_c1c] using (nb077_compact_fv_empty_0071 x F)

theorem nb077_compact_fv_empty_0072 (F : Class) (I : Class) : (nb077_alpha_dummy_055 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0176 (F : Class) (I : Class) : (nb077_alpha_dummy_055 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_055, fv_syn_c1c] using (nb077_compact_fv_empty_0072 F I)

theorem nb077_compact_fv_empty_0073 (x : Var) (F : Class) : (nb077_alpha_dummy_056 x F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0177 (x : Var) (F : Class) : (nb077_alpha_dummy_056 x F) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_056, fv_syn_c1c] using (nb077_compact_fv_empty_0073 x F)

theorem nb077_compact_envfresh_0009 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_083 F I), (nb077_alpha_dummy_086 x)), ((nb077_alpha_dummy_082 F I), (nb077_alpha_dummy_085 x)), ((nb077_alpha_dummy_081 F I), (nb077_alpha_dummy_084 x)), ((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I), (nb077_alpha_dummy_077 x)), ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)), ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_073 F I), (nb077_alpha_dummy_074 x)), ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_083 F I) (nb077_alpha_dummy_086 x) (nb077_wpp_notmem_0148 F I) (nb077_wpp_notmem_0149 x) (TEnvFresh.consFresh (nb077_alpha_dummy_082 F I) (nb077_alpha_dummy_085 x) (nb077_wpp_notmem_0150 F I) (nb077_wpp_notmem_0151 x) (TEnvFresh.consFresh (nb077_alpha_dummy_081 F I) (nb077_alpha_dummy_084 x) (nb077_wpp_notmem_0152 F I) (nb077_wpp_notmem_0153 x) (TEnvFresh.consFresh (nb077_alpha_dummy_079 F I) (nb077_alpha_dummy_080 x) (nb077_wpp_notmem_0154 F I) (nb077_wpp_notmem_0155 x) (TEnvFresh.consFresh (nb077_alpha_dummy_075 F I) (nb077_alpha_dummy_077 x) (nb077_wpp_notmem_0156 F I) (nb077_wpp_notmem_0157 x) (TEnvFresh.consFresh (nb077_alpha_dummy_076 F I) (nb077_alpha_dummy_078 x) (nb077_wpp_notmem_0158 F I) (nb077_wpp_notmem_0159 x) (TEnvFresh.consFresh (nb077_alpha_dummy_068 F I) (nb077_alpha_dummy_070 x) (nb077_wpp_notmem_0160 F I) (nb077_wpp_notmem_0161 x) (TEnvFresh.consFresh (nb077_alpha_dummy_067 F I) (nb077_alpha_dummy_069 x) (nb077_wpp_notmem_0162 F I) (nb077_wpp_notmem_0163 x) (TEnvFresh.consFresh (nb077_alpha_dummy_073 F I) (nb077_alpha_dummy_074 x) (nb077_wpp_notmem_0164 F I) (nb077_wpp_notmem_0165 x) (TEnvFresh.consFresh (nb077_alpha_dummy_071 F I) (nb077_alpha_dummy_072 x) (nb077_wpp_notmem_0166 F I) (nb077_wpp_notmem_0167 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0168 F I) (nb077_wpp_notmem_0169 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0170 F I) (nb077_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0172 F I) (nb077_wpp_notmem_0173 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0174 F I) (nb077_wpp_notmem_0175 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0176 F I) (nb077_wpp_notmem_0177 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0030 F I) (nb077_wpp_notmem_0031 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0032 F I) (nb077_wpp_notmem_0033 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0034 F I) (nb077_wpp_notmem_0035 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0036 F I) (nb077_wpp_notmem_0037 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0038 F I) (nb077_wpp_notmem_0039 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0040 F I) (nb077_wpp_notmem_0041 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0042 F I) (nb077_wpp_notmem_0043 x F I) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
