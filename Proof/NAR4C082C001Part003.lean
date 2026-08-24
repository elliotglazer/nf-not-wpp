import NAR4C082C001Part002

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

theorem nb082_wpp_notmem_0026 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_021 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_021, fv_syn_c0] using (nb082_compact_fv_empty_0000 A B R)

theorem nb082_wpp_notmem_0027 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_024 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_024, fv_syn_c0] using (nb082_compact_fv_empty_0001 A B R p)

theorem nb082_wpp_notmem_0028 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_020 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_020, fv_syn_c0] using (nb082_compact_fv_empty_0002 A B R)

theorem nb082_wpp_notmem_0029 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_023 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_023, fv_syn_c0] using (nb082_compact_fv_empty_0003 A B R p)

theorem nb082_wpp_notmem_0030 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_019 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_019, fv_syn_c0] using (nb082_compact_fv_empty_0004 A B R)

theorem nb082_wpp_notmem_0031 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_022 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_022, fv_syn_c0] using (nb082_compact_fv_empty_0005 A B R p)

theorem nb082_wpp_notmem_0032 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_017 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_017, fv_syn_c0] using (nb082_compact_fv_empty_0006 A B R)

theorem nb082_wpp_notmem_0033 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_018 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_018, fv_syn_c0] using (nb082_compact_fv_empty_0007 A B R p)

theorem nb082_wpp_notmem_0034 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_013 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_013, fv_syn_c0] using (nb082_compact_fv_empty_0008 A B R)

theorem nb082_wpp_notmem_0035 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_015 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_015, fv_syn_c0] using (nb082_compact_fv_empty_0009 A B R p)

theorem nb082_wpp_notmem_0036 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_014 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_014, fv_syn_c0] using (nb082_compact_fv_empty_0010 A B R)

theorem nb082_wpp_notmem_0037 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_016 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_016, fv_syn_c0] using (nb082_compact_fv_empty_0011 A B R p)

theorem nb082_wpp_notmem_0038 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_006 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_006, fv_syn_c0] using (nb082_compact_fv_empty_0012 A B R)

theorem nb082_wpp_notmem_0039 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_008 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_008, fv_syn_c0] using (nb082_compact_fv_empty_0013 A B R p)

theorem nb082_wpp_notmem_0040 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_005 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_005, fv_syn_c0] using (nb082_compact_fv_empty_0014 A B R)

theorem nb082_wpp_notmem_0041 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_007 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_007, fv_syn_c0] using (nb082_compact_fv_empty_0015 A B R p)

theorem nb082_wpp_notmem_0042 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_011 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_011, fv_syn_c0] using (nb082_compact_fv_empty_0016 A B R)

theorem nb082_wpp_notmem_0043 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_012 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_012, fv_syn_c0] using (nb082_compact_fv_empty_0017 A B R p)

theorem nb082_wpp_notmem_0044 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_009 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_009, fv_syn_c0] using (nb082_compact_fv_empty_0018 A B R)

theorem nb082_wpp_notmem_0045 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_010 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_010, fv_syn_c0] using (nb082_compact_fv_empty_0019 A B R p)

theorem nb082_wpp_notmem_0046 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_001, fv_syn_c0] using (nb082_compact_fv_empty_0020 A B R)

theorem nb082_wpp_notmem_0047 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_002, fv_syn_c0] using (nb082_compact_fv_empty_0021 A B R p)

theorem nb082_wpp_notmem_0048 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_000, fv_syn_c0] using (nb082_compact_fv_empty_0022 A B R)

theorem nb082_wpp_notmem_0049 (p : Var) : p ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb082_compact_fv_empty_0023 p)

theorem nb082_wpp_notmem_0050 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_003 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_003, fv_syn_c0] using (nb082_compact_fv_empty_0024 A B R)

theorem nb082_wpp_notmem_0051 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_004 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_004, fv_syn_c0] using (nb082_compact_fv_empty_0025 A B R p)

theorem nb082_compact_envfresh_0001 (A : Class) (B : Class) (R : Class) (p : Var) : TEnvFresh [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)), ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)), ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)), ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb082_alpha_dummy_021 A B R) (nb082_alpha_dummy_024 A B R p) (nb082_wpp_notmem_0026 A B R) (nb082_wpp_notmem_0027 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_020 A B R) (nb082_alpha_dummy_023 A B R p) (nb082_wpp_notmem_0028 A B R) (nb082_wpp_notmem_0029 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_019 A B R) (nb082_alpha_dummy_022 A B R p) (nb082_wpp_notmem_0030 A B R) (nb082_wpp_notmem_0031 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_017 A B R) (nb082_alpha_dummy_018 A B R p) (nb082_wpp_notmem_0032 A B R) (nb082_wpp_notmem_0033 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_013 A B R) (nb082_alpha_dummy_015 A B R p) (nb082_wpp_notmem_0034 A B R) (nb082_wpp_notmem_0035 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_014 A B R) (nb082_alpha_dummy_016 A B R p) (nb082_wpp_notmem_0036 A B R) (nb082_wpp_notmem_0037 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_006 A B R) (nb082_alpha_dummy_008 A B R p) (nb082_wpp_notmem_0038 A B R) (nb082_wpp_notmem_0039 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_005 A B R) (nb082_alpha_dummy_007 A B R p) (nb082_wpp_notmem_0040 A B R) (nb082_wpp_notmem_0041 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_011 A B R) (nb082_alpha_dummy_012 A B R p) (nb082_wpp_notmem_0042 A B R) (nb082_wpp_notmem_0043 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_009 A B R) (nb082_alpha_dummy_010 A B R p) (nb082_wpp_notmem_0044 A B R) (nb082_wpp_notmem_0045 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_001 A B R) (nb082_alpha_dummy_002 A B R p) (nb082_wpp_notmem_0046 A B R) (nb082_wpp_notmem_0047 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_000 A B R) p (nb082_wpp_notmem_0048 A B R) (nb082_wpp_notmem_0049 p) (TEnvFresh.consFresh (nb082_alpha_dummy_003 A B R) (nb082_alpha_dummy_004 A B R p) (nb082_wpp_notmem_0050 A B R) (nb082_wpp_notmem_0051 A B R p) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb082_wpp_refl_0001 (A : Class) (B : Class) (R : Class) (p : Var) : TReflOn [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)), ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)), ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)), ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0001 A B R p)

theorem nb082_wpp_notmem_0052 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_017 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_017, fv_syn_cnnc] using (nb082_compact_fv_empty_0006 A B R)

theorem nb082_wpp_notmem_0053 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_018 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_018, fv_syn_cnnc] using (nb082_compact_fv_empty_0007 A B R p)

theorem nb082_wpp_notmem_0054 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_013 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_013, fv_syn_cnnc] using (nb082_compact_fv_empty_0008 A B R)

theorem nb082_wpp_notmem_0055 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_015 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_015, fv_syn_cnnc] using (nb082_compact_fv_empty_0009 A B R p)

theorem nb082_wpp_notmem_0056 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_014 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_014, fv_syn_cnnc] using (nb082_compact_fv_empty_0010 A B R)

theorem nb082_wpp_notmem_0057 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_016 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_016, fv_syn_cnnc] using (nb082_compact_fv_empty_0011 A B R p)

theorem nb082_wpp_notmem_0058 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_006 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_006, fv_syn_cnnc] using (nb082_compact_fv_empty_0012 A B R)

theorem nb082_wpp_notmem_0059 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_008 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_008, fv_syn_cnnc] using (nb082_compact_fv_empty_0013 A B R p)

theorem nb082_wpp_notmem_0060 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_005 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_005, fv_syn_cnnc] using (nb082_compact_fv_empty_0014 A B R)

theorem nb082_wpp_notmem_0061 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_007 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_007, fv_syn_cnnc] using (nb082_compact_fv_empty_0015 A B R p)

theorem nb082_wpp_notmem_0062 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_011 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_011, fv_syn_cnnc] using (nb082_compact_fv_empty_0016 A B R)

theorem nb082_wpp_notmem_0063 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_012 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_012, fv_syn_cnnc] using (nb082_compact_fv_empty_0017 A B R p)

theorem nb082_wpp_notmem_0064 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_009 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_009, fv_syn_cnnc] using (nb082_compact_fv_empty_0018 A B R)

theorem nb082_wpp_notmem_0065 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_010 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_010, fv_syn_cnnc] using (nb082_compact_fv_empty_0019 A B R p)

theorem nb082_wpp_notmem_0066 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_001, fv_syn_cnnc] using (nb082_compact_fv_empty_0020 A B R)

theorem nb082_wpp_notmem_0067 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_002, fv_syn_cnnc] using (nb082_compact_fv_empty_0021 A B R p)

theorem nb082_wpp_notmem_0068 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_000, fv_syn_cnnc] using (nb082_compact_fv_empty_0022 A B R)

theorem nb082_wpp_notmem_0069 (p : Var) : p ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb082_compact_fv_empty_0023 p)

theorem nb082_wpp_notmem_0070 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_003 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_003, fv_syn_cnnc] using (nb082_compact_fv_empty_0024 A B R)

theorem nb082_wpp_notmem_0071 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_004 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_004, fv_syn_cnnc] using (nb082_compact_fv_empty_0025 A B R p)

theorem nb082_compact_envfresh_0002 (A : Class) (B : Class) (R : Class) (p : Var) : TEnvFresh [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb082_alpha_dummy_017 A B R) (nb082_alpha_dummy_018 A B R p) (nb082_wpp_notmem_0052 A B R) (nb082_wpp_notmem_0053 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_013 A B R) (nb082_alpha_dummy_015 A B R p) (nb082_wpp_notmem_0054 A B R) (nb082_wpp_notmem_0055 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_014 A B R) (nb082_alpha_dummy_016 A B R p) (nb082_wpp_notmem_0056 A B R) (nb082_wpp_notmem_0057 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_006 A B R) (nb082_alpha_dummy_008 A B R p) (nb082_wpp_notmem_0058 A B R) (nb082_wpp_notmem_0059 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_005 A B R) (nb082_alpha_dummy_007 A B R p) (nb082_wpp_notmem_0060 A B R) (nb082_wpp_notmem_0061 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_011 A B R) (nb082_alpha_dummy_012 A B R p) (nb082_wpp_notmem_0062 A B R) (nb082_wpp_notmem_0063 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_009 A B R) (nb082_alpha_dummy_010 A B R p) (nb082_wpp_notmem_0064 A B R) (nb082_wpp_notmem_0065 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_001 A B R) (nb082_alpha_dummy_002 A B R p) (nb082_wpp_notmem_0066 A B R) (nb082_wpp_notmem_0067 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_000 A B R) p (nb082_wpp_notmem_0068 A B R) (nb082_wpp_notmem_0069 p) (TEnvFresh.consFresh (nb082_alpha_dummy_003 A B R) (nb082_alpha_dummy_004 A B R p) (nb082_wpp_notmem_0070 A B R) (nb082_wpp_notmem_0071 A B R p) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb082_wpp_refl_0002 (A : Class) (B : Class) (R : Class) (p : Var) : TReflOn [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0002 A B R p)

theorem nb082_compact_fv_empty_0026 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_039 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0072 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_039 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_039, fv_syn_c1c] using (nb082_compact_fv_empty_0026 A B R)

theorem nb082_compact_fv_empty_0027 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_040 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0073 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_040 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_040, fv_syn_c1c] using (nb082_compact_fv_empty_0027 A B R p)

theorem nb082_compact_fv_empty_0028 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_037 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0074 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_037 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_037, fv_syn_c1c] using (nb082_compact_fv_empty_0028 A B R)

theorem nb082_compact_fv_empty_0029 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_038 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0075 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_038 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_038, fv_syn_c1c] using (nb082_compact_fv_empty_0029 A B R p)

theorem nb082_compact_fv_empty_0030 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_035 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0076 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_035 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_035, fv_syn_c1c] using (nb082_compact_fv_empty_0030 A B R)

theorem nb082_compact_fv_empty_0031 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_036 A B R p) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb082_wpp_notmem_0077 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_036 A B R p) ∉ ((syn_c1c)).fv := by
  simpa only [nb082_alpha_dummy_036, fv_syn_c1c] using (nb082_compact_fv_empty_0031 A B R p)

theorem nb082_compact_envfresh_0003 (A : Class) (B : Class) (R : Class) (p : Var) : TEnvFresh [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)), ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)), ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)), ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)), ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb082_alpha_dummy_021 A B R) (nb082_alpha_dummy_024 A B R p) (nb082_wpp_notmem_0000 A B R) (nb082_wpp_notmem_0001 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_020 A B R) (nb082_alpha_dummy_023 A B R p) (nb082_wpp_notmem_0002 A B R) (nb082_wpp_notmem_0003 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_019 A B R) (nb082_alpha_dummy_022 A B R p) (nb082_wpp_notmem_0004 A B R) (nb082_wpp_notmem_0005 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_017 A B R) (nb082_alpha_dummy_018 A B R p) (nb082_wpp_notmem_0006 A B R) (nb082_wpp_notmem_0007 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_013 A B R) (nb082_alpha_dummy_015 A B R p) (nb082_wpp_notmem_0008 A B R) (nb082_wpp_notmem_0009 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_014 A B R) (nb082_alpha_dummy_016 A B R p) (nb082_wpp_notmem_0010 A B R) (nb082_wpp_notmem_0011 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_039 A B R) (nb082_alpha_dummy_040 A B R p) (nb082_wpp_notmem_0072 A B R) (nb082_wpp_notmem_0073 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_037 A B R) (nb082_alpha_dummy_038 A B R p) (nb082_wpp_notmem_0074 A B R) (nb082_wpp_notmem_0075 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_006 A B R) (nb082_alpha_dummy_008 A B R p) (nb082_wpp_notmem_0012 A B R) (nb082_wpp_notmem_0013 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_005 A B R) (nb082_alpha_dummy_007 A B R p) (nb082_wpp_notmem_0014 A B R) (nb082_wpp_notmem_0015 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_035 A B R) (nb082_alpha_dummy_036 A B R p) (nb082_wpp_notmem_0076 A B R) (nb082_wpp_notmem_0077 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_009 A B R) (nb082_alpha_dummy_010 A B R p) (nb082_wpp_notmem_0018 A B R) (nb082_wpp_notmem_0019 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_001 A B R) (nb082_alpha_dummy_002 A B R p) (nb082_wpp_notmem_0020 A B R) (nb082_wpp_notmem_0021 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_000 A B R) p (nb082_wpp_notmem_0022 A B R) (nb082_wpp_notmem_0023 p) (TEnvFresh.consFresh (nb082_alpha_dummy_003 A B R) (nb082_alpha_dummy_004 A B R p) (nb082_wpp_notmem_0024 A B R) (nb082_wpp_notmem_0025 A B R p) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb082_wpp_refl_0003 (A : Class) (B : Class) (R : Class) (p : Var) : TReflOn [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)), ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)), ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)), ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)), ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0003 A B R p)

theorem nb082_wpp_notmem_0078 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_039 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_039, fv_syn_c0] using (nb082_compact_fv_empty_0026 A B R)

theorem nb082_wpp_notmem_0079 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_040 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_040, fv_syn_c0] using (nb082_compact_fv_empty_0027 A B R p)

theorem nb082_wpp_notmem_0080 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_037 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_037, fv_syn_c0] using (nb082_compact_fv_empty_0028 A B R)

theorem nb082_wpp_notmem_0081 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_038 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_038, fv_syn_c0] using (nb082_compact_fv_empty_0029 A B R p)

theorem nb082_wpp_notmem_0082 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_035 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_035, fv_syn_c0] using (nb082_compact_fv_empty_0030 A B R)

theorem nb082_wpp_notmem_0083 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_036 A B R p) ∉ ((syn_c0)).fv := by
  simpa only [nb082_alpha_dummy_036, fv_syn_c0] using (nb082_compact_fv_empty_0031 A B R p)

theorem nb082_compact_envfresh_0004 (A : Class) (B : Class) (R : Class) (p : Var) : TEnvFresh [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)), ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)), ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)), ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)), ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb082_alpha_dummy_021 A B R) (nb082_alpha_dummy_024 A B R p) (nb082_wpp_notmem_0026 A B R) (nb082_wpp_notmem_0027 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_020 A B R) (nb082_alpha_dummy_023 A B R p) (nb082_wpp_notmem_0028 A B R) (nb082_wpp_notmem_0029 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_019 A B R) (nb082_alpha_dummy_022 A B R p) (nb082_wpp_notmem_0030 A B R) (nb082_wpp_notmem_0031 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_017 A B R) (nb082_alpha_dummy_018 A B R p) (nb082_wpp_notmem_0032 A B R) (nb082_wpp_notmem_0033 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_013 A B R) (nb082_alpha_dummy_015 A B R p) (nb082_wpp_notmem_0034 A B R) (nb082_wpp_notmem_0035 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_014 A B R) (nb082_alpha_dummy_016 A B R p) (nb082_wpp_notmem_0036 A B R) (nb082_wpp_notmem_0037 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_039 A B R) (nb082_alpha_dummy_040 A B R p) (nb082_wpp_notmem_0078 A B R) (nb082_wpp_notmem_0079 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_037 A B R) (nb082_alpha_dummy_038 A B R p) (nb082_wpp_notmem_0080 A B R) (nb082_wpp_notmem_0081 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_006 A B R) (nb082_alpha_dummy_008 A B R p) (nb082_wpp_notmem_0038 A B R) (nb082_wpp_notmem_0039 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_005 A B R) (nb082_alpha_dummy_007 A B R p) (nb082_wpp_notmem_0040 A B R) (nb082_wpp_notmem_0041 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_035 A B R) (nb082_alpha_dummy_036 A B R p) (nb082_wpp_notmem_0082 A B R) (nb082_wpp_notmem_0083 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_009 A B R) (nb082_alpha_dummy_010 A B R p) (nb082_wpp_notmem_0044 A B R) (nb082_wpp_notmem_0045 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_001 A B R) (nb082_alpha_dummy_002 A B R p) (nb082_wpp_notmem_0046 A B R) (nb082_wpp_notmem_0047 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_000 A B R) p (nb082_wpp_notmem_0048 A B R) (nb082_wpp_notmem_0049 p) (TEnvFresh.consFresh (nb082_alpha_dummy_003 A B R) (nb082_alpha_dummy_004 A B R p) (nb082_wpp_notmem_0050 A B R) (nb082_wpp_notmem_0051 A B R p) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb082_wpp_refl_0004 (A : Class) (B : Class) (R : Class) (p : Var) : TReflOn [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)), ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)), ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)), ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)), ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0004 A B R p)

theorem nb082_wpp_notmem_0084 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_039 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_039, fv_syn_cnnc] using (nb082_compact_fv_empty_0026 A B R)

theorem nb082_wpp_notmem_0085 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_040 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_040, fv_syn_cnnc] using (nb082_compact_fv_empty_0027 A B R p)

theorem nb082_wpp_notmem_0086 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_037 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_037, fv_syn_cnnc] using (nb082_compact_fv_empty_0028 A B R)

theorem nb082_wpp_notmem_0087 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_038 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_038, fv_syn_cnnc] using (nb082_compact_fv_empty_0029 A B R p)

theorem nb082_wpp_notmem_0088 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_035 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_035, fv_syn_cnnc] using (nb082_compact_fv_empty_0030 A B R)

theorem nb082_wpp_notmem_0089 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_036 A B R p) ∉ ((syn_cnnc)).fv := by
  simpa only [nb082_alpha_dummy_036, fv_syn_cnnc] using (nb082_compact_fv_empty_0031 A B R p)

theorem nb082_compact_envfresh_0005 (A : Class) (B : Class) (R : Class) (p : Var) : TEnvFresh [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)), ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb082_alpha_dummy_017 A B R) (nb082_alpha_dummy_018 A B R p) (nb082_wpp_notmem_0052 A B R) (nb082_wpp_notmem_0053 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_013 A B R) (nb082_alpha_dummy_015 A B R p) (nb082_wpp_notmem_0054 A B R) (nb082_wpp_notmem_0055 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_014 A B R) (nb082_alpha_dummy_016 A B R p) (nb082_wpp_notmem_0056 A B R) (nb082_wpp_notmem_0057 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_039 A B R) (nb082_alpha_dummy_040 A B R p) (nb082_wpp_notmem_0084 A B R) (nb082_wpp_notmem_0085 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_037 A B R) (nb082_alpha_dummy_038 A B R p) (nb082_wpp_notmem_0086 A B R) (nb082_wpp_notmem_0087 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_006 A B R) (nb082_alpha_dummy_008 A B R p) (nb082_wpp_notmem_0058 A B R) (nb082_wpp_notmem_0059 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_005 A B R) (nb082_alpha_dummy_007 A B R p) (nb082_wpp_notmem_0060 A B R) (nb082_wpp_notmem_0061 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_035 A B R) (nb082_alpha_dummy_036 A B R p) (nb082_wpp_notmem_0088 A B R) (nb082_wpp_notmem_0089 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_009 A B R) (nb082_alpha_dummy_010 A B R p) (nb082_wpp_notmem_0064 A B R) (nb082_wpp_notmem_0065 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_001 A B R) (nb082_alpha_dummy_002 A B R p) (nb082_wpp_notmem_0066 A B R) (nb082_wpp_notmem_0067 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_000 A B R) p (nb082_wpp_notmem_0068 A B R) (nb082_wpp_notmem_0069 p) (TEnvFresh.consFresh (nb082_alpha_dummy_003 A B R) (nb082_alpha_dummy_004 A B R p) (nb082_wpp_notmem_0070 A B R) (nb082_wpp_notmem_0071 A B R p) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb082_wpp_refl_0005 (A : Class) (B : Class) (R : Class) (p : Var) : TReflOn [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)), ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)), ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)), ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)), ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0005 A B R p)

theorem nb082_wpp_notmem_0090 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_037 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_037, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0028 A B R)

theorem nb082_wpp_notmem_0091 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_038 A B R p) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0029 A B R p)

theorem nb082_wpp_notmem_0092 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_006 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0012 A B R)

theorem nb082_wpp_notmem_0093 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_008 A B R p) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0013 A B R p)

theorem nb082_wpp_notmem_0094 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_005 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0014 A B R)

theorem nb082_wpp_notmem_0095 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_007 A B R p) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0015 A B R p)

theorem nb082_wpp_notmem_0096 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_035 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_035, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0030 A B R)

theorem nb082_wpp_notmem_0097 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_036 A B R p) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_036, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0031 A B R p)

theorem nb082_wpp_notmem_0098 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_009 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0018 A B R)

theorem nb082_wpp_notmem_0099 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_010 A B R p) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0019 A B R p)

theorem nb082_wpp_notmem_0100 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_001 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0020 A B R)

theorem nb082_wpp_notmem_0101 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_002 A B R p) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0021 A B R p)

theorem nb082_wpp_notmem_0102 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_000 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0022 A B R)

theorem nb082_wpp_notmem_0103 (p : Var) : p ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0023 p)

theorem nb082_wpp_notmem_0104 (A : Class) (B : Class) (R : Class) : (nb082_alpha_dummy_003 A B R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0024 A B R)

theorem nb082_wpp_notmem_0105 (A : Class) (B : Class) (R : Class) (p : Var) : (nb082_alpha_dummy_004 A B R p) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb082_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb082_compact_fv_empty_0025 A B R p)

theorem nb082_compact_envfresh_0006 (A : Class) (B : Class) (R : Class) (p : Var) : TEnvFresh [((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb082_alpha_dummy_037 A B R) (nb082_alpha_dummy_038 A B R p) (nb082_wpp_notmem_0090 A B R) (nb082_wpp_notmem_0091 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_006 A B R) (nb082_alpha_dummy_008 A B R p) (nb082_wpp_notmem_0092 A B R) (nb082_wpp_notmem_0093 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_005 A B R) (nb082_alpha_dummy_007 A B R p) (nb082_wpp_notmem_0094 A B R) (nb082_wpp_notmem_0095 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_035 A B R) (nb082_alpha_dummy_036 A B R p) (nb082_wpp_notmem_0096 A B R) (nb082_wpp_notmem_0097 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_009 A B R) (nb082_alpha_dummy_010 A B R p) (nb082_wpp_notmem_0098 A B R) (nb082_wpp_notmem_0099 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_001 A B R) (nb082_alpha_dummy_002 A B R p) (nb082_wpp_notmem_0100 A B R) (nb082_wpp_notmem_0101 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_000 A B R) p (nb082_wpp_notmem_0102 A B R) (nb082_wpp_notmem_0103 p) (TEnvFresh.consFresh (nb082_alpha_dummy_003 A B R) (nb082_alpha_dummy_004 A B R p) (nb082_wpp_notmem_0104 A B R) (nb082_wpp_notmem_0105 A B R p) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb082_wpp_refl_0006 (A : Class) (B : Class) (R : Class) (p : Var) : TReflOn [((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)), ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)), ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)), ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)), ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)), ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)), ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0006 A B R p)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
