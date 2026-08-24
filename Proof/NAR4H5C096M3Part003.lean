import NAR4H5C096M3Part002

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

theorem nb096_wpp_notmem_0162 (D : Class) (R : Class) : (nb096_alpha_dummy_071 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_071, fv_syn_c0] using (nb096_compact_fv_empty_0048 D R)

theorem nb096_wpp_notmem_0163 (R : Class) (q : Var) : (nb096_alpha_dummy_072 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_072, fv_syn_c0] using (nb096_compact_fv_empty_0049 R q)

theorem nb096_wpp_notmem_0164 (D : Class) (R : Class) : (nb096_alpha_dummy_069 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_069, fv_syn_c0] using (nb096_compact_fv_empty_0050 D R)

theorem nb096_wpp_notmem_0165 (R : Class) (q : Var) : (nb096_alpha_dummy_070 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_070, fv_syn_c0] using (nb096_compact_fv_empty_0051 R q)

theorem nb096_wpp_notmem_0166 (D : Class) (R : Class) : (nb096_alpha_dummy_052 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_052, fv_syn_c0] using (nb096_compact_fv_empty_0052 D R)

theorem nb096_wpp_notmem_0167 (R : Class) (q : Var) : (nb096_alpha_dummy_054 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_054, fv_syn_c0] using (nb096_compact_fv_empty_0053 R q)

theorem nb096_wpp_notmem_0168 (D : Class) (R : Class) : (nb096_alpha_dummy_051 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_051, fv_syn_c0] using (nb096_compact_fv_empty_0054 D R)

theorem nb096_wpp_notmem_0169 (R : Class) (q : Var) : (nb096_alpha_dummy_053 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_053, fv_syn_c0] using (nb096_compact_fv_empty_0055 R q)

theorem nb096_wpp_notmem_0170 (D : Class) (R : Class) : (nb096_alpha_dummy_049 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_049, fv_syn_c0] using (nb096_compact_fv_empty_0056 D R)

theorem nb096_wpp_notmem_0171 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_050 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_050, fv_syn_c0] using (nb096_compact_fv_empty_0057 D R q)

theorem nb096_wpp_notmem_0172 (D : Class) (R : Class) : (nb096_alpha_dummy_047 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_047, fv_syn_c0] using (nb096_compact_fv_empty_0058 D R)

theorem nb096_wpp_notmem_0173 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_048 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_048, fv_syn_c0] using (nb096_compact_fv_empty_0059 D R q)

theorem nb096_wpp_notmem_0174 (D : Class) (R : Class) : (nb096_alpha_dummy_045 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_045, fv_syn_c0] using (nb096_compact_fv_empty_0060 D R)

theorem nb096_wpp_notmem_0175 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_046 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_046, fv_syn_c0] using (nb096_compact_fv_empty_0061 D R q)

theorem nb096_wpp_notmem_0176 (D : Class) (R : Class) : (nb096_alpha_dummy_042 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_042, fv_syn_c0] using (nb096_compact_fv_empty_0062 D R)

theorem nb096_wpp_notmem_0177 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_044 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_044, fv_syn_c0] using (nb096_compact_fv_empty_0063 D R q)

theorem nb096_wpp_notmem_0178 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_041, fv_syn_c0] using (nb096_compact_fv_empty_0064 D R)

theorem nb096_wpp_notmem_0179 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_043, fv_syn_c0] using (nb096_compact_fv_empty_0065 D R q)

theorem nb096_compact_envfresh_0010 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_081 D R) (nb096_alpha_dummy_084 R q) (nb096_wpp_notmem_0146 D R) (nb096_wpp_notmem_0147 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_080 D R) (nb096_alpha_dummy_083 R q) (nb096_wpp_notmem_0148 D R) (nb096_wpp_notmem_0149 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_079 D R) (nb096_alpha_dummy_082 R q) (nb096_wpp_notmem_0150 D R) (nb096_wpp_notmem_0151 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_077 D R) (nb096_alpha_dummy_078 R q) (nb096_wpp_notmem_0152 D R) (nb096_wpp_notmem_0153 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_073 D R) (nb096_alpha_dummy_075 R q) (nb096_wpp_notmem_0154 D R) (nb096_wpp_notmem_0155 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_074 D R) (nb096_alpha_dummy_076 R q) (nb096_wpp_notmem_0156 D R) (nb096_wpp_notmem_0157 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_066 D R) (nb096_alpha_dummy_068 R q) (nb096_wpp_notmem_0158 D R) (nb096_wpp_notmem_0159 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_065 D R) (nb096_alpha_dummy_067 R q) (nb096_wpp_notmem_0160 D R) (nb096_wpp_notmem_0161 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_071 D R) (nb096_alpha_dummy_072 R q) (nb096_wpp_notmem_0162 D R) (nb096_wpp_notmem_0163 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_069 D R) (nb096_alpha_dummy_070 R q) (nb096_wpp_notmem_0164 D R) (nb096_wpp_notmem_0165 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_052 D R) (nb096_alpha_dummy_054 R q) (nb096_wpp_notmem_0166 D R) (nb096_wpp_notmem_0167 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_051 D R) (nb096_alpha_dummy_053 R q) (nb096_wpp_notmem_0168 D R) (nb096_wpp_notmem_0169 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q) (nb096_wpp_notmem_0170 D R) (nb096_wpp_notmem_0171 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q) (nb096_wpp_notmem_0172 D R) (nb096_wpp_notmem_0173 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q) (nb096_wpp_notmem_0174 D R) (nb096_wpp_notmem_0175 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0176 D R) (nb096_wpp_notmem_0177 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0178 D R) (nb096_wpp_notmem_0179 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0046 D R) (nb096_wpp_notmem_0047 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0048 D R) (nb096_wpp_notmem_0049 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0050 D R) (nb096_wpp_notmem_0051 D R q) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb096_wpp_refl_0009 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0010 D R q)

theorem nb096_wpp_notmem_0180 (D : Class) (R : Class) : (nb096_alpha_dummy_077 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_077, fv_syn_cnnc] using (nb096_compact_fv_empty_0038 D R)

theorem nb096_wpp_notmem_0181 (R : Class) (q : Var) : (nb096_alpha_dummy_078 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_078, fv_syn_cnnc] using (nb096_compact_fv_empty_0039 R q)

theorem nb096_wpp_notmem_0182 (D : Class) (R : Class) : (nb096_alpha_dummy_073 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_073, fv_syn_cnnc] using (nb096_compact_fv_empty_0040 D R)

theorem nb096_wpp_notmem_0183 (R : Class) (q : Var) : (nb096_alpha_dummy_075 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_075, fv_syn_cnnc] using (nb096_compact_fv_empty_0041 R q)

theorem nb096_wpp_notmem_0184 (D : Class) (R : Class) : (nb096_alpha_dummy_074 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_074, fv_syn_cnnc] using (nb096_compact_fv_empty_0042 D R)

theorem nb096_wpp_notmem_0185 (R : Class) (q : Var) : (nb096_alpha_dummy_076 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_076, fv_syn_cnnc] using (nb096_compact_fv_empty_0043 R q)

theorem nb096_wpp_notmem_0186 (D : Class) (R : Class) : (nb096_alpha_dummy_066 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_066, fv_syn_cnnc] using (nb096_compact_fv_empty_0044 D R)

theorem nb096_wpp_notmem_0187 (R : Class) (q : Var) : (nb096_alpha_dummy_068 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_068, fv_syn_cnnc] using (nb096_compact_fv_empty_0045 R q)

theorem nb096_wpp_notmem_0188 (D : Class) (R : Class) : (nb096_alpha_dummy_065 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_065, fv_syn_cnnc] using (nb096_compact_fv_empty_0046 D R)

theorem nb096_wpp_notmem_0189 (R : Class) (q : Var) : (nb096_alpha_dummy_067 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_067, fv_syn_cnnc] using (nb096_compact_fv_empty_0047 R q)

theorem nb096_wpp_notmem_0190 (D : Class) (R : Class) : (nb096_alpha_dummy_071 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_071, fv_syn_cnnc] using (nb096_compact_fv_empty_0048 D R)

theorem nb096_wpp_notmem_0191 (R : Class) (q : Var) : (nb096_alpha_dummy_072 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_072, fv_syn_cnnc] using (nb096_compact_fv_empty_0049 R q)

theorem nb096_wpp_notmem_0192 (D : Class) (R : Class) : (nb096_alpha_dummy_069 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_069, fv_syn_cnnc] using (nb096_compact_fv_empty_0050 D R)

theorem nb096_wpp_notmem_0193 (R : Class) (q : Var) : (nb096_alpha_dummy_070 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_070, fv_syn_cnnc] using (nb096_compact_fv_empty_0051 R q)

theorem nb096_wpp_notmem_0194 (D : Class) (R : Class) : (nb096_alpha_dummy_052 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_052, fv_syn_cnnc] using (nb096_compact_fv_empty_0052 D R)

theorem nb096_wpp_notmem_0195 (R : Class) (q : Var) : (nb096_alpha_dummy_054 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_054, fv_syn_cnnc] using (nb096_compact_fv_empty_0053 R q)

theorem nb096_wpp_notmem_0196 (D : Class) (R : Class) : (nb096_alpha_dummy_051 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_051, fv_syn_cnnc] using (nb096_compact_fv_empty_0054 D R)

theorem nb096_wpp_notmem_0197 (R : Class) (q : Var) : (nb096_alpha_dummy_053 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_053, fv_syn_cnnc] using (nb096_compact_fv_empty_0055 R q)

theorem nb096_wpp_notmem_0198 (D : Class) (R : Class) : (nb096_alpha_dummy_049 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_049, fv_syn_cnnc] using (nb096_compact_fv_empty_0056 D R)

theorem nb096_wpp_notmem_0199 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_050 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_050, fv_syn_cnnc] using (nb096_compact_fv_empty_0057 D R q)

theorem nb096_wpp_notmem_0200 (D : Class) (R : Class) : (nb096_alpha_dummy_047 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_047, fv_syn_cnnc] using (nb096_compact_fv_empty_0058 D R)

theorem nb096_wpp_notmem_0201 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_048 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_048, fv_syn_cnnc] using (nb096_compact_fv_empty_0059 D R q)

theorem nb096_wpp_notmem_0202 (D : Class) (R : Class) : (nb096_alpha_dummy_045 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_045, fv_syn_cnnc] using (nb096_compact_fv_empty_0060 D R)

theorem nb096_wpp_notmem_0203 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_046 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_046, fv_syn_cnnc] using (nb096_compact_fv_empty_0061 D R q)

theorem nb096_wpp_notmem_0204 (D : Class) (R : Class) : (nb096_alpha_dummy_042 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_042, fv_syn_cnnc] using (nb096_compact_fv_empty_0062 D R)

theorem nb096_wpp_notmem_0205 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_044 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_044, fv_syn_cnnc] using (nb096_compact_fv_empty_0063 D R q)

theorem nb096_wpp_notmem_0206 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_041, fv_syn_cnnc] using (nb096_compact_fv_empty_0064 D R)

theorem nb096_wpp_notmem_0207 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_043, fv_syn_cnnc] using (nb096_compact_fv_empty_0065 D R q)

theorem nb096_compact_envfresh_0011 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_077 D R) (nb096_alpha_dummy_078 R q) (nb096_wpp_notmem_0180 D R) (nb096_wpp_notmem_0181 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_073 D R) (nb096_alpha_dummy_075 R q) (nb096_wpp_notmem_0182 D R) (nb096_wpp_notmem_0183 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_074 D R) (nb096_alpha_dummy_076 R q) (nb096_wpp_notmem_0184 D R) (nb096_wpp_notmem_0185 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_066 D R) (nb096_alpha_dummy_068 R q) (nb096_wpp_notmem_0186 D R) (nb096_wpp_notmem_0187 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_065 D R) (nb096_alpha_dummy_067 R q) (nb096_wpp_notmem_0188 D R) (nb096_wpp_notmem_0189 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_071 D R) (nb096_alpha_dummy_072 R q) (nb096_wpp_notmem_0190 D R) (nb096_wpp_notmem_0191 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_069 D R) (nb096_alpha_dummy_070 R q) (nb096_wpp_notmem_0192 D R) (nb096_wpp_notmem_0193 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_052 D R) (nb096_alpha_dummy_054 R q) (nb096_wpp_notmem_0194 D R) (nb096_wpp_notmem_0195 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_051 D R) (nb096_alpha_dummy_053 R q) (nb096_wpp_notmem_0196 D R) (nb096_wpp_notmem_0197 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q) (nb096_wpp_notmem_0198 D R) (nb096_wpp_notmem_0199 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q) (nb096_wpp_notmem_0200 D R) (nb096_wpp_notmem_0201 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q) (nb096_wpp_notmem_0202 D R) (nb096_wpp_notmem_0203 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0204 D R) (nb096_wpp_notmem_0205 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0206 D R) (nb096_wpp_notmem_0207 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0066 D R) (nb096_wpp_notmem_0067 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0068 D R) (nb096_wpp_notmem_0069 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0070 D R) (nb096_wpp_notmem_0071 D R q) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb096_wpp_refl_0010 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0011 D R q)

noncomputable def nb096_split_alpha_0003 (D : Class) (R : Class) (q : Var) : TAlphaWff [((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_071 D R)) (Class.cab (nb096_alpha_dummy_065 D R) (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R)) (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R)) (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))) (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_071 D R)) (Class.cab (nb096_alpha_dummy_065 D R) (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R)) (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R)) (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))))) (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_072 R q)) (Class.cab (nb096_alpha_dummy_067 R q) (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q)) (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q)) (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))) (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_072 R q)) (Class.cab (nb096_alpha_dummy_067 R q) (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q)) (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q)) (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0064 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0065 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0061 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0063 R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪ ((Class.cv (nb096_alpha_dummy_051 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪ ((Class.cv (nb096_alpha_dummy_053 R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0066 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0067 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0066 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0067 R q) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_066 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_068 R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0070 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0071 R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0070 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0071 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0008 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0074 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0075 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0072 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0073 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0078 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0079 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0076 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0077 R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0074 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0075 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0072 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0073 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0078 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0079 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0076 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0077 R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0009 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0082 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0083 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0080 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0081 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0082 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0083 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0080 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0081 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0086 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0087 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0084 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0085 R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0086 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0087 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0084 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0085 R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0010 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0010 D R q)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0060 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0062 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0064 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0065 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0061 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0063 R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪ ((Class.cv (nb096_alpha_dummy_051 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪ ((Class.cv (nb096_alpha_dummy_053 R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0066 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0067 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0066 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0067 R q) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_066 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_068 R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0070 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0071 R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0070 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0071 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0008 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0074 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0075 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0072 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0073 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0078 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0079 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0076 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0077 R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0074 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0075 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0072 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0073 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0078 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0079 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0076 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0077 R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0009 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0082 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0083 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0080 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0081 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0082 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0083 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0080 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0081 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0086 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0087 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0084 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0085 R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0086 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0087 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0084 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0085 R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0010 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0010 D R q))))))))))))))))))))))))))))

theorem nb096_compact_fv_empty_0066 (D : Class) (R : Class) : (nb096_alpha_dummy_099 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0208 (D : Class) (R : Class) : (nb096_alpha_dummy_099 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_099, fv_syn_c1c] using (nb096_compact_fv_empty_0066 D R)

theorem nb096_compact_fv_empty_0067 (R : Class) (q : Var) : (nb096_alpha_dummy_100 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0209 (R : Class) (q : Var) : (nb096_alpha_dummy_100 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_100, fv_syn_c1c] using (nb096_compact_fv_empty_0067 R q)

theorem nb096_compact_fv_empty_0068 (D : Class) (R : Class) : (nb096_alpha_dummy_097 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0210 (D : Class) (R : Class) : (nb096_alpha_dummy_097 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_097, fv_syn_c1c] using (nb096_compact_fv_empty_0068 D R)

theorem nb096_compact_fv_empty_0069 (R : Class) (q : Var) : (nb096_alpha_dummy_098 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0211 (R : Class) (q : Var) : (nb096_alpha_dummy_098 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_098, fv_syn_c1c] using (nb096_compact_fv_empty_0069 R q)

theorem nb096_compact_fv_empty_0070 (D : Class) (R : Class) : (nb096_alpha_dummy_095 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0212 (D : Class) (R : Class) : (nb096_alpha_dummy_095 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_095, fv_syn_c1c] using (nb096_compact_fv_empty_0070 D R)

theorem nb096_compact_fv_empty_0071 (R : Class) (q : Var) : (nb096_alpha_dummy_096 R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0213 (R : Class) (q : Var) : (nb096_alpha_dummy_096 R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_096, fv_syn_c1c] using (nb096_compact_fv_empty_0071 R q)

theorem nb096_compact_envfresh_0012 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_081 D R) (nb096_alpha_dummy_084 R q) (nb096_wpp_notmem_0112 D R) (nb096_wpp_notmem_0113 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_080 D R) (nb096_alpha_dummy_083 R q) (nb096_wpp_notmem_0114 D R) (nb096_wpp_notmem_0115 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_079 D R) (nb096_alpha_dummy_082 R q) (nb096_wpp_notmem_0116 D R) (nb096_wpp_notmem_0117 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_077 D R) (nb096_alpha_dummy_078 R q) (nb096_wpp_notmem_0118 D R) (nb096_wpp_notmem_0119 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_073 D R) (nb096_alpha_dummy_075 R q) (nb096_wpp_notmem_0120 D R) (nb096_wpp_notmem_0121 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_074 D R) (nb096_alpha_dummy_076 R q) (nb096_wpp_notmem_0122 D R) (nb096_wpp_notmem_0123 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_099 D R) (nb096_alpha_dummy_100 R q) (nb096_wpp_notmem_0208 D R) (nb096_wpp_notmem_0209 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_097 D R) (nb096_alpha_dummy_098 R q) (nb096_wpp_notmem_0210 D R) (nb096_wpp_notmem_0211 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_066 D R) (nb096_alpha_dummy_068 R q) (nb096_wpp_notmem_0124 D R) (nb096_wpp_notmem_0125 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_065 D R) (nb096_alpha_dummy_067 R q) (nb096_wpp_notmem_0126 D R) (nb096_wpp_notmem_0127 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_095 D R) (nb096_alpha_dummy_096 R q) (nb096_wpp_notmem_0212 D R) (nb096_wpp_notmem_0213 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_069 D R) (nb096_alpha_dummy_070 R q) (nb096_wpp_notmem_0130 D R) (nb096_wpp_notmem_0131 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_052 D R) (nb096_alpha_dummy_054 R q) (nb096_wpp_notmem_0132 D R) (nb096_wpp_notmem_0133 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_051 D R) (nb096_alpha_dummy_053 R q) (nb096_wpp_notmem_0134 D R) (nb096_wpp_notmem_0135 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q) (nb096_wpp_notmem_0136 D R) (nb096_wpp_notmem_0137 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q) (nb096_wpp_notmem_0138 D R) (nb096_wpp_notmem_0139 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q) (nb096_wpp_notmem_0140 D R) (nb096_wpp_notmem_0141 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0142 D R) (nb096_wpp_notmem_0143 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0144 D R) (nb096_wpp_notmem_0145 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0020 D R) (nb096_wpp_notmem_0021 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0022 D R) (nb096_wpp_notmem_0023 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0024 D R) (nb096_wpp_notmem_0025 D R q) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb096_wpp_refl_0011 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0012 D R q)

theorem nb096_wpp_notmem_0214 (D : Class) (R : Class) : (nb096_alpha_dummy_099 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_099, fv_syn_c0] using (nb096_compact_fv_empty_0066 D R)

theorem nb096_wpp_notmem_0215 (R : Class) (q : Var) : (nb096_alpha_dummy_100 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_100, fv_syn_c0] using (nb096_compact_fv_empty_0067 R q)

theorem nb096_wpp_notmem_0216 (D : Class) (R : Class) : (nb096_alpha_dummy_097 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_097, fv_syn_c0] using (nb096_compact_fv_empty_0068 D R)

theorem nb096_wpp_notmem_0217 (R : Class) (q : Var) : (nb096_alpha_dummy_098 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_098, fv_syn_c0] using (nb096_compact_fv_empty_0069 R q)

theorem nb096_wpp_notmem_0218 (D : Class) (R : Class) : (nb096_alpha_dummy_095 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_095, fv_syn_c0] using (nb096_compact_fv_empty_0070 D R)

theorem nb096_wpp_notmem_0219 (R : Class) (q : Var) : (nb096_alpha_dummy_096 R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_096, fv_syn_c0] using (nb096_compact_fv_empty_0071 R q)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

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

theorem nb096_compact_envfresh_0013 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_081 D R) (nb096_alpha_dummy_084 R q) (nb096_wpp_notmem_0146 D R) (nb096_wpp_notmem_0147 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_080 D R) (nb096_alpha_dummy_083 R q) (nb096_wpp_notmem_0148 D R) (nb096_wpp_notmem_0149 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_079 D R) (nb096_alpha_dummy_082 R q) (nb096_wpp_notmem_0150 D R) (nb096_wpp_notmem_0151 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_077 D R) (nb096_alpha_dummy_078 R q) (nb096_wpp_notmem_0152 D R) (nb096_wpp_notmem_0153 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_073 D R) (nb096_alpha_dummy_075 R q) (nb096_wpp_notmem_0154 D R) (nb096_wpp_notmem_0155 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_074 D R) (nb096_alpha_dummy_076 R q) (nb096_wpp_notmem_0156 D R) (nb096_wpp_notmem_0157 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_099 D R) (nb096_alpha_dummy_100 R q) (nb096_wpp_notmem_0214 D R) (nb096_wpp_notmem_0215 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_097 D R) (nb096_alpha_dummy_098 R q) (nb096_wpp_notmem_0216 D R) (nb096_wpp_notmem_0217 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_066 D R) (nb096_alpha_dummy_068 R q) (nb096_wpp_notmem_0158 D R) (nb096_wpp_notmem_0159 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_065 D R) (nb096_alpha_dummy_067 R q) (nb096_wpp_notmem_0160 D R) (nb096_wpp_notmem_0161 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_095 D R) (nb096_alpha_dummy_096 R q) (nb096_wpp_notmem_0218 D R) (nb096_wpp_notmem_0219 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_069 D R) (nb096_alpha_dummy_070 R q) (nb096_wpp_notmem_0164 D R) (nb096_wpp_notmem_0165 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_052 D R) (nb096_alpha_dummy_054 R q) (nb096_wpp_notmem_0166 D R) (nb096_wpp_notmem_0167 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_051 D R) (nb096_alpha_dummy_053 R q) (nb096_wpp_notmem_0168 D R) (nb096_wpp_notmem_0169 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q) (nb096_wpp_notmem_0170 D R) (nb096_wpp_notmem_0171 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q) (nb096_wpp_notmem_0172 D R) (nb096_wpp_notmem_0173 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q) (nb096_wpp_notmem_0174 D R) (nb096_wpp_notmem_0175 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0176 D R) (nb096_wpp_notmem_0177 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0178 D R) (nb096_wpp_notmem_0179 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0046 D R) (nb096_wpp_notmem_0047 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0048 D R) (nb096_wpp_notmem_0049 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0050 D R) (nb096_wpp_notmem_0051 D R q) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb096_wpp_refl_0012 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0013 D R q)

theorem nb096_wpp_notmem_0220 (D : Class) (R : Class) : (nb096_alpha_dummy_099 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_099, fv_syn_cnnc] using (nb096_compact_fv_empty_0066 D R)

theorem nb096_wpp_notmem_0221 (R : Class) (q : Var) : (nb096_alpha_dummy_100 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_100, fv_syn_cnnc] using (nb096_compact_fv_empty_0067 R q)

theorem nb096_wpp_notmem_0222 (D : Class) (R : Class) : (nb096_alpha_dummy_097 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_097, fv_syn_cnnc] using (nb096_compact_fv_empty_0068 D R)

theorem nb096_wpp_notmem_0223 (R : Class) (q : Var) : (nb096_alpha_dummy_098 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_098, fv_syn_cnnc] using (nb096_compact_fv_empty_0069 R q)

theorem nb096_wpp_notmem_0224 (D : Class) (R : Class) : (nb096_alpha_dummy_095 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_095, fv_syn_cnnc] using (nb096_compact_fv_empty_0070 D R)

theorem nb096_wpp_notmem_0225 (R : Class) (q : Var) : (nb096_alpha_dummy_096 R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_096, fv_syn_cnnc] using (nb096_compact_fv_empty_0071 R q)

theorem nb096_compact_envfresh_0014 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_077 D R) (nb096_alpha_dummy_078 R q) (nb096_wpp_notmem_0180 D R) (nb096_wpp_notmem_0181 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_073 D R) (nb096_alpha_dummy_075 R q) (nb096_wpp_notmem_0182 D R) (nb096_wpp_notmem_0183 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_074 D R) (nb096_alpha_dummy_076 R q) (nb096_wpp_notmem_0184 D R) (nb096_wpp_notmem_0185 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_099 D R) (nb096_alpha_dummy_100 R q) (nb096_wpp_notmem_0220 D R) (nb096_wpp_notmem_0221 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_097 D R) (nb096_alpha_dummy_098 R q) (nb096_wpp_notmem_0222 D R) (nb096_wpp_notmem_0223 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_066 D R) (nb096_alpha_dummy_068 R q) (nb096_wpp_notmem_0186 D R) (nb096_wpp_notmem_0187 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_065 D R) (nb096_alpha_dummy_067 R q) (nb096_wpp_notmem_0188 D R) (nb096_wpp_notmem_0189 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_095 D R) (nb096_alpha_dummy_096 R q) (nb096_wpp_notmem_0224 D R) (nb096_wpp_notmem_0225 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_069 D R) (nb096_alpha_dummy_070 R q) (nb096_wpp_notmem_0192 D R) (nb096_wpp_notmem_0193 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_052 D R) (nb096_alpha_dummy_054 R q) (nb096_wpp_notmem_0194 D R) (nb096_wpp_notmem_0195 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_051 D R) (nb096_alpha_dummy_053 R q) (nb096_wpp_notmem_0196 D R) (nb096_wpp_notmem_0197 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q) (nb096_wpp_notmem_0198 D R) (nb096_wpp_notmem_0199 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q) (nb096_wpp_notmem_0200 D R) (nb096_wpp_notmem_0201 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q) (nb096_wpp_notmem_0202 D R) (nb096_wpp_notmem_0203 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0204 D R) (nb096_wpp_notmem_0205 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0206 D R) (nb096_wpp_notmem_0207 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0066 D R) (nb096_wpp_notmem_0067 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0068 D R) (nb096_wpp_notmem_0069 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0070 D R) (nb096_wpp_notmem_0071 D R q) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))

noncomputable def nb096_wpp_refl_0013 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0014 D R q)

noncomputable def nb096_split_alpha_0004 (D : Class) (R : Class) (q : Var) : TAlphaWff [((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_099 D R)) (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))) (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_099 D R)) (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))))) (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_100 R q)) (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))) (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_100 R q)) (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0066 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0067 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0066 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0067 R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0096 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0097 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0094 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0095 R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_066 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_068 R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0070 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0071 R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0070 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0071 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0011 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0074 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0075 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0072 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0073 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0078 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0079 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0076 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0077 R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0074 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0075 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0072 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0073 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0078 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0079 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0076 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0077 R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0012 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0082 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0083 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0080 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0081 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0082 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0083 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0080 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0081 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0086 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0087 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0084 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0085 R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0086 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0087 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0084 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0085 R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0013 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0013 D R q)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0066 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0067 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0066 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0067 R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0096 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0097 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0094 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0095 R q) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_066 D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_068 R q))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0070 D R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0071 R q) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0070 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0071 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (nb096_wpp_refl_0011 D R q))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0074 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0075 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0072 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0073 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0078 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0079 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0076 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0077 R q) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0074 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0075 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0072 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0073 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0078 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0079 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0076 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0077 R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (nb096_wpp_refl_0012 D R q))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0082 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0083 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0080 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0081 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0082 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0083 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0080 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0081 R q) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0086 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0087 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0084 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0085 R q) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0086 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0087 R q) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0084 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0085 R q) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0013 D R q))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0069 R q) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (nb096_wpp_refl_0013 D R q))))))))))))))))))))

theorem nb096_wpp_notmem_0226 (D : Class) (R : Class) : (nb096_alpha_dummy_097 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_097, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0068 D R)

theorem nb096_wpp_notmem_0227 (R : Class) (q : Var) : (nb096_alpha_dummy_098 R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_098, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0069 R q)

theorem nb096_wpp_notmem_0228 (D : Class) (R : Class) : (nb096_alpha_dummy_066 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_066, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0044 D R)

theorem nb096_wpp_notmem_0229 (R : Class) (q : Var) : (nb096_alpha_dummy_068 R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_068, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0045 R q)

theorem nb096_wpp_notmem_0230 (D : Class) (R : Class) : (nb096_alpha_dummy_065 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_065, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0046 D R)

theorem nb096_wpp_notmem_0231 (R : Class) (q : Var) : (nb096_alpha_dummy_067 R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_067, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0047 R q)

theorem nb096_wpp_notmem_0232 (D : Class) (R : Class) : (nb096_alpha_dummy_095 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_095, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0070 D R)

theorem nb096_wpp_notmem_0233 (R : Class) (q : Var) : (nb096_alpha_dummy_096 R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_096, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0071 R q)

theorem nb096_wpp_notmem_0234 (D : Class) (R : Class) : (nb096_alpha_dummy_069 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_069, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0050 D R)

theorem nb096_wpp_notmem_0235 (R : Class) (q : Var) : (nb096_alpha_dummy_070 R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_070, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0051 R q)

theorem nb096_wpp_notmem_0236 (D : Class) (R : Class) : (nb096_alpha_dummy_052 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_052, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0052 D R)

theorem nb096_wpp_notmem_0237 (R : Class) (q : Var) : (nb096_alpha_dummy_054 R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_054, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0053 R q)

theorem nb096_wpp_notmem_0238 (D : Class) (R : Class) : (nb096_alpha_dummy_051 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_051, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0054 D R)

theorem nb096_wpp_notmem_0239 (R : Class) (q : Var) : (nb096_alpha_dummy_053 R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_053, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0055 R q)

theorem nb096_wpp_notmem_0240 (D : Class) (R : Class) : (nb096_alpha_dummy_049 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_049, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0056 D R)

theorem nb096_wpp_notmem_0241 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_050 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_050, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0057 D R q)

theorem nb096_wpp_notmem_0242 (D : Class) (R : Class) : (nb096_alpha_dummy_047 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_047, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0058 D R)

theorem nb096_wpp_notmem_0243 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_048 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_048, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0059 D R q)

theorem nb096_wpp_notmem_0244 (D : Class) (R : Class) : (nb096_alpha_dummy_045 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0060 D R)

theorem nb096_wpp_notmem_0245 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_046 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0061 D R q)

theorem nb096_wpp_notmem_0246 (D : Class) (R : Class) : (nb096_alpha_dummy_042 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_042, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0062 D R)

theorem nb096_wpp_notmem_0247 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_044 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0063 D R q)

theorem nb096_wpp_notmem_0248 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_041, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0064 D R)

theorem nb096_wpp_notmem_0249 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_043, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0065 D R q)

theorem nb096_compact_envfresh_0015 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_097 D R) (nb096_alpha_dummy_098 R q) (nb096_wpp_notmem_0226 D R) (nb096_wpp_notmem_0227 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_066 D R) (nb096_alpha_dummy_068 R q) (nb096_wpp_notmem_0228 D R) (nb096_wpp_notmem_0229 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_065 D R) (nb096_alpha_dummy_067 R q) (nb096_wpp_notmem_0230 D R) (nb096_wpp_notmem_0231 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_095 D R) (nb096_alpha_dummy_096 R q) (nb096_wpp_notmem_0232 D R) (nb096_wpp_notmem_0233 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_069 D R) (nb096_alpha_dummy_070 R q) (nb096_wpp_notmem_0234 D R) (nb096_wpp_notmem_0235 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_052 D R) (nb096_alpha_dummy_054 R q) (nb096_wpp_notmem_0236 D R) (nb096_wpp_notmem_0237 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_051 D R) (nb096_alpha_dummy_053 R q) (nb096_wpp_notmem_0238 D R) (nb096_wpp_notmem_0239 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q) (nb096_wpp_notmem_0240 D R) (nb096_wpp_notmem_0241 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q) (nb096_wpp_notmem_0242 D R) (nb096_wpp_notmem_0243 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q) (nb096_wpp_notmem_0244 D R) (nb096_wpp_notmem_0245 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0246 D R) (nb096_wpp_notmem_0247 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0248 D R) (nb096_wpp_notmem_0249 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0100 D R) (nb096_wpp_notmem_0101 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0102 D R) (nb096_wpp_notmem_0103 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0104 D R) (nb096_wpp_notmem_0105 D R q) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))

noncomputable def nb096_wpp_refl_0014 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0015 D R q)

theorem nb096_focused_notmem_0015 (D : Class) (R : Class) : (nb096_alpha_dummy_052 D R) ∉ R.fv := by
  change freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv) 1 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))

theorem nb096_wpp_notmem_0250 (D : Class) (R : Class) : (nb096_alpha_dummy_052 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_052, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0015 D R) (nb096_compact_fv_empty_0052 D R))

theorem nb096_focused_notmem_0016 (R : Class) (q : Var) : (nb096_alpha_dummy_054 R q) ∉ R.fv := by
  change freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv) 1 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))

theorem nb096_wpp_notmem_0251 (R : Class) (q : Var) : (nb096_alpha_dummy_054 R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_054, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0016 R q) (nb096_compact_fv_empty_0053 R q))

theorem nb096_focused_notmem_0017 (D : Class) (R : Class) : (nb096_alpha_dummy_051 D R) ∉ R.fv := by
  change freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))

theorem nb096_wpp_notmem_0252 (D : Class) (R : Class) : (nb096_alpha_dummy_051 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_051, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0017 D R) (nb096_compact_fv_empty_0054 D R))

theorem nb096_focused_notmem_0018 (R : Class) (q : Var) : (nb096_alpha_dummy_053 R q) ∉ R.fv := by
  change freshVar (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))

theorem nb096_wpp_notmem_0253 (R : Class) (q : Var) : (nb096_alpha_dummy_053 R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_053, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0018 R q) (nb096_compact_fv_empty_0055 R q))

theorem nb096_focused_notmem_0019 (D : Class) (R : Class) : (nb096_alpha_dummy_049 D R) ∉ R.fv := by
  change freshVar ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu))))))))))

theorem nb096_wpp_notmem_0254 (D : Class) (R : Class) : (nb096_alpha_dummy_049 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_049, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0019 D R) (nb096_compact_fv_empty_0056 D R))

theorem nb096_focused_notmem_0020 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_050 D R q) ∉ R.fv := by
  change freshVar ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu))))))))))

theorem nb096_wpp_notmem_0255 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_050 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_050, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0020 D R q) (nb096_compact_fv_empty_0057 D R q))

theorem nb096_focused_notmem_0021 (D : Class) (R : Class) : (nb096_alpha_dummy_047 D R) ∉ R.fv := by
  change freshVar (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv ∪ ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))

theorem nb096_wpp_notmem_0256 (D : Class) (R : Class) : (nb096_alpha_dummy_047 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_047, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0021 D R) (nb096_compact_fv_empty_0058 D R))

theorem nb096_focused_notmem_0022 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_048 D R q) ∉ R.fv := by
  change freshVar (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv ∪ ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (((fv_syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))

theorem nb096_wpp_notmem_0257 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_048 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_048, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0022 D R q) (nb096_compact_fv_empty_0059 D R q))

theorem nb096_focused_notmem_0023 (D : Class) (R : Class) : (nb096_alpha_dummy_045 D R) ∉ R.fv := by
  change freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => ((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu))))))))))))

theorem nb096_wpp_notmem_0258 (D : Class) (R : Class) : (nb096_alpha_dummy_045 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_045, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0023 D R) (nb096_compact_fv_empty_0060 D R))

theorem nb096_focused_notmem_0024 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_046 D R q) ∉ R.fv := by
  change freshVar (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => ((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

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

theorem nb096_wpp_notmem_0259 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_046 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_046, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0024 D R q) (nb096_compact_fv_empty_0061 D R q))

theorem nb096_focused_notmem_0025 (D : Class) (R : Class) : (nb096_alpha_dummy_042 D R) ∉ R.fv := by
  change freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) 1 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => Finset.mem_union_right _ (((fv_syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))))

theorem nb096_wpp_notmem_0260 (D : Class) (R : Class) : (nb096_alpha_dummy_042 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_042, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0025 D R) (nb096_compact_fv_empty_0062 D R))

theorem nb096_focused_notmem_0026 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_044 D R q) ∉ R.fv := by
  change freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) 1 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => Finset.mem_union_right _ (((fv_syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))))

theorem nb096_wpp_notmem_0261 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_044 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_044, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0026 D R q) (nb096_compact_fv_empty_0063 D R q))

theorem nb096_focused_notmem_0027 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∉ R.fv := by
  change freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))))

theorem nb096_wpp_notmem_0262 (D : Class) (R : Class) : (nb096_alpha_dummy_041 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_041, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0027 D R) (nb096_compact_fv_empty_0064 D R))

theorem nb096_focused_notmem_0028 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∉ R.fv := by
  change freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))))

theorem nb096_wpp_notmem_0263 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_043 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_043, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0028 D R q) (nb096_compact_fv_empty_0065 D R q))

theorem nb096_focused_notmem_0029 (D : Class) (R : Class) : (nb096_alpha_dummy_001 D R) ∉ R.fv := by
  change freshVar (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))))

theorem nb096_wpp_notmem_0264 (D : Class) (R : Class) : (nb096_alpha_dummy_001 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_001, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0029 D R) (nb096_compact_fv_empty_0020 D R))

theorem nb096_focused_notmem_0030 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_002 D R q) ∉ R.fv := by
  change freshVar (({q} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))))

theorem nb096_wpp_notmem_0265 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_002 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_002, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0030 D R q) (nb096_compact_fv_empty_0021 D R q))

theorem nb096_focused_notmem_0031 (D : Class) (R : Class) : (nb096_alpha_dummy_000 D R) ∉ R.fv := by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb096_wpp_notmem_0266 (D : Class) (R : Class) : (nb096_alpha_dummy_000 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_000, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0031 D R) (nb096_compact_fv_empty_0022 D R))

theorem nb096_wpp_notmem_0267 (R : Class) (q : Var) (dv_R_q : q ∉ R.fv) : q ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro dv_R_q (nb096_compact_fv_empty_0023 q))

theorem nb096_focused_notmem_0032 (D : Class) (R : Class) : (nb096_alpha_dummy_003 D R) ∉ R.fv := by
  change freshVar (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ({(nb096_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D))) (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D))) (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))))).symm ▸ (Finset.mem_union_right _ (((fv_wff_classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))))))))))

theorem nb096_wpp_notmem_0268 (D : Class) (R : Class) : (nb096_alpha_dummy_003 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_003, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0032 D R) (nb096_compact_fv_empty_0024 D R))

theorem nb096_focused_notmem_0033 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_004 D R q) ∉ R.fv := by
  change freshVar (({q} : Finset Var) ∪ ({(nb096_alpha_dummy_002 D R q)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D))) (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))))).fv) 0 ∉ R.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D))) (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))))).symm ▸ (Finset.mem_union_right _ (((fv_wff_classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).symm ▸ (((fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q))))).symm ▸ (Finset.mem_union_left _ (((fv_syn_ccnv (syn_cdif R (syn_cid))).symm ▸ (((fv_syn_cdif R (syn_cid)).symm ▸ (Finset.mem_union_left _ (hu)))))))))))))))))))))

theorem nb096_wpp_notmem_0269 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_004 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_004, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using (And.intro (nb096_focused_notmem_0033 D R q) (nb096_compact_fv_empty_0025 D R q))

theorem nb096_compact_envfresh_0016 (D : Class) (R : Class) (q : Var) (dv_R_q : q ∉ R.fv) : TEnvFresh [((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_052 D R) (nb096_alpha_dummy_054 R q) (nb096_wpp_notmem_0250 D R) (nb096_wpp_notmem_0251 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_051 D R) (nb096_alpha_dummy_053 R q) (nb096_wpp_notmem_0252 D R) (nb096_wpp_notmem_0253 R q) (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q) (nb096_wpp_notmem_0254 D R) (nb096_wpp_notmem_0255 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q) (nb096_wpp_notmem_0256 D R) (nb096_wpp_notmem_0257 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q) (nb096_wpp_notmem_0258 D R) (nb096_wpp_notmem_0259 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0260 D R) (nb096_wpp_notmem_0261 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0262 D R) (nb096_wpp_notmem_0263 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0264 D R) (nb096_wpp_notmem_0265 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0266 D R) (nb096_wpp_notmem_0267 R q dv_R_q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0268 D R) (nb096_wpp_notmem_0269 D R q) (TEnvFresh.nil ((syn_ccnv (syn_cdif R (syn_cid)))).fv)))))))))))

noncomputable def nb096_wpp_refl_0015 (D : Class) (R : Class) (q : Var) (dv_R_q : q ∉ R.fv) : TReflOn [((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0016 D R q dv_R_q)

theorem nb096_compact_fv_empty_0072 (D : Class) (R : Class) : (nb096_alpha_dummy_117 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0270 (D : Class) (R : Class) : (nb096_alpha_dummy_117 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_117, fv_syn_c1c] using (nb096_compact_fv_empty_0072 D R)

theorem nb096_compact_fv_empty_0073 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_120 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0271 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_120 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_120, fv_syn_c1c] using (nb096_compact_fv_empty_0073 D R q)

theorem nb096_compact_fv_empty_0074 (D : Class) (R : Class) : (nb096_alpha_dummy_116 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0272 (D : Class) (R : Class) : (nb096_alpha_dummy_116 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_116, fv_syn_c1c] using (nb096_compact_fv_empty_0074 D R)

theorem nb096_compact_fv_empty_0075 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_119 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0273 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_119 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_119, fv_syn_c1c] using (nb096_compact_fv_empty_0075 D R q)

theorem nb096_compact_fv_empty_0076 (D : Class) (R : Class) : (nb096_alpha_dummy_115 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0274 (D : Class) (R : Class) : (nb096_alpha_dummy_115 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_115, fv_syn_c1c] using (nb096_compact_fv_empty_0076 D R)

theorem nb096_compact_fv_empty_0077 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_118 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0275 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_118 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_118, fv_syn_c1c] using (nb096_compact_fv_empty_0077 D R q)

theorem nb096_compact_fv_empty_0078 (D : Class) (R : Class) : (nb096_alpha_dummy_113 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0276 (D : Class) (R : Class) : (nb096_alpha_dummy_113 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_113, fv_syn_c1c] using (nb096_compact_fv_empty_0078 D R)

theorem nb096_compact_fv_empty_0079 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_114 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0277 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_114 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_114, fv_syn_c1c] using (nb096_compact_fv_empty_0079 D R q)

theorem nb096_compact_fv_empty_0080 (D : Class) (R : Class) : (nb096_alpha_dummy_109 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0278 (D : Class) (R : Class) : (nb096_alpha_dummy_109 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_109, fv_syn_c1c] using (nb096_compact_fv_empty_0080 D R)

theorem nb096_compact_fv_empty_0081 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_111 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0279 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_111 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_111, fv_syn_c1c] using (nb096_compact_fv_empty_0081 D R q)

theorem nb096_compact_fv_empty_0082 (D : Class) (R : Class) : (nb096_alpha_dummy_110 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0280 (D : Class) (R : Class) : (nb096_alpha_dummy_110 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_110, fv_syn_c1c] using (nb096_compact_fv_empty_0082 D R)

theorem nb096_compact_fv_empty_0083 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_112 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0281 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_112 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_112, fv_syn_c1c] using (nb096_compact_fv_empty_0083 D R q)

theorem nb096_compact_fv_empty_0084 (D : Class) (R : Class) : (nb096_alpha_dummy_102 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0282 (D : Class) (R : Class) : (nb096_alpha_dummy_102 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_102, fv_syn_c1c] using (nb096_compact_fv_empty_0084 D R)

theorem nb096_compact_fv_empty_0085 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_104 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0283 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_104 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_104, fv_syn_c1c] using (nb096_compact_fv_empty_0085 D R q)

theorem nb096_compact_fv_empty_0086 (D : Class) (R : Class) : (nb096_alpha_dummy_101 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0284 (D : Class) (R : Class) : (nb096_alpha_dummy_101 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_101, fv_syn_c1c] using (nb096_compact_fv_empty_0086 D R)

theorem nb096_compact_fv_empty_0087 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_103 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0285 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_103 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_103, fv_syn_c1c] using (nb096_compact_fv_empty_0087 D R q)

theorem nb096_compact_fv_empty_0088 (D : Class) (R : Class) : (nb096_alpha_dummy_107 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0286 (D : Class) (R : Class) : (nb096_alpha_dummy_107 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_107, fv_syn_c1c] using (nb096_compact_fv_empty_0088 D R)

theorem nb096_compact_fv_empty_0089 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_108 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0287 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_108 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_108, fv_syn_c1c] using (nb096_compact_fv_empty_0089 D R q)

theorem nb096_compact_fv_empty_0090 (D : Class) (R : Class) : (nb096_alpha_dummy_105 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0288 (D : Class) (R : Class) : (nb096_alpha_dummy_105 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_105, fv_syn_c1c] using (nb096_compact_fv_empty_0090 D R)

theorem nb096_compact_fv_empty_0091 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_106 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0289 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_106 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_106, fv_syn_c1c] using (nb096_compact_fv_empty_0091 D R q)

theorem nb096_compact_envfresh_0017 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)), ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)), ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)), ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_117 D R) (nb096_alpha_dummy_120 D R q) (nb096_wpp_notmem_0270 D R) (nb096_wpp_notmem_0271 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_116 D R) (nb096_alpha_dummy_119 D R q) (nb096_wpp_notmem_0272 D R) (nb096_wpp_notmem_0273 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_115 D R) (nb096_alpha_dummy_118 D R q) (nb096_wpp_notmem_0274 D R) (nb096_wpp_notmem_0275 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_113 D R) (nb096_alpha_dummy_114 D R q) (nb096_wpp_notmem_0276 D R) (nb096_wpp_notmem_0277 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_109 D R) (nb096_alpha_dummy_111 D R q) (nb096_wpp_notmem_0278 D R) (nb096_wpp_notmem_0279 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_110 D R) (nb096_alpha_dummy_112 D R q) (nb096_wpp_notmem_0280 D R) (nb096_wpp_notmem_0281 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_102 D R) (nb096_alpha_dummy_104 D R q) (nb096_wpp_notmem_0282 D R) (nb096_wpp_notmem_0283 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_101 D R) (nb096_alpha_dummy_103 D R q) (nb096_wpp_notmem_0284 D R) (nb096_wpp_notmem_0285 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_107 D R) (nb096_alpha_dummy_108 D R q) (nb096_wpp_notmem_0286 D R) (nb096_wpp_notmem_0287 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_105 D R) (nb096_alpha_dummy_106 D R q) (nb096_wpp_notmem_0288 D R) (nb096_wpp_notmem_0289 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0142 D R) (nb096_wpp_notmem_0143 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0144 D R) (nb096_wpp_notmem_0145 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0020 D R) (nb096_wpp_notmem_0021 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0022 D R) (nb096_wpp_notmem_0023 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0024 D R) (nb096_wpp_notmem_0025 D R q) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb096_wpp_refl_0016 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)), ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)), ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)), ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0017 D R q)

theorem nb096_wpp_notmem_0290 (D : Class) (R : Class) : (nb096_alpha_dummy_117 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_117, fv_syn_c0] using (nb096_compact_fv_empty_0072 D R)

theorem nb096_wpp_notmem_0291 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_120 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_120, fv_syn_c0] using (nb096_compact_fv_empty_0073 D R q)

theorem nb096_wpp_notmem_0292 (D : Class) (R : Class) : (nb096_alpha_dummy_116 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_116, fv_syn_c0] using (nb096_compact_fv_empty_0074 D R)

theorem nb096_wpp_notmem_0293 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_119 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_119, fv_syn_c0] using (nb096_compact_fv_empty_0075 D R q)

theorem nb096_wpp_notmem_0294 (D : Class) (R : Class) : (nb096_alpha_dummy_115 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_115, fv_syn_c0] using (nb096_compact_fv_empty_0076 D R)

theorem nb096_wpp_notmem_0295 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_118 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_118, fv_syn_c0] using (nb096_compact_fv_empty_0077 D R q)

theorem nb096_wpp_notmem_0296 (D : Class) (R : Class) : (nb096_alpha_dummy_113 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_113, fv_syn_c0] using (nb096_compact_fv_empty_0078 D R)

theorem nb096_wpp_notmem_0297 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_114 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_114, fv_syn_c0] using (nb096_compact_fv_empty_0079 D R q)

theorem nb096_wpp_notmem_0298 (D : Class) (R : Class) : (nb096_alpha_dummy_109 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_109, fv_syn_c0] using (nb096_compact_fv_empty_0080 D R)

theorem nb096_wpp_notmem_0299 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_111 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_111, fv_syn_c0] using (nb096_compact_fv_empty_0081 D R q)

theorem nb096_wpp_notmem_0300 (D : Class) (R : Class) : (nb096_alpha_dummy_110 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_110, fv_syn_c0] using (nb096_compact_fv_empty_0082 D R)

theorem nb096_wpp_notmem_0301 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_112 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_112, fv_syn_c0] using (nb096_compact_fv_empty_0083 D R q)

theorem nb096_wpp_notmem_0302 (D : Class) (R : Class) : (nb096_alpha_dummy_102 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_102, fv_syn_c0] using (nb096_compact_fv_empty_0084 D R)

theorem nb096_wpp_notmem_0303 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_104 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_104, fv_syn_c0] using (nb096_compact_fv_empty_0085 D R q)

theorem nb096_wpp_notmem_0304 (D : Class) (R : Class) : (nb096_alpha_dummy_101 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_101, fv_syn_c0] using (nb096_compact_fv_empty_0086 D R)

theorem nb096_wpp_notmem_0305 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_103 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_103, fv_syn_c0] using (nb096_compact_fv_empty_0087 D R q)

theorem nb096_wpp_notmem_0306 (D : Class) (R : Class) : (nb096_alpha_dummy_107 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_107, fv_syn_c0] using (nb096_compact_fv_empty_0088 D R)

theorem nb096_wpp_notmem_0307 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_108 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_108, fv_syn_c0] using (nb096_compact_fv_empty_0089 D R q)

theorem nb096_wpp_notmem_0308 (D : Class) (R : Class) : (nb096_alpha_dummy_105 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_105, fv_syn_c0] using (nb096_compact_fv_empty_0090 D R)

theorem nb096_wpp_notmem_0309 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_106 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_106, fv_syn_c0] using (nb096_compact_fv_empty_0091 D R q)

theorem nb096_compact_envfresh_0018 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)), ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)), ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)), ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_117 D R) (nb096_alpha_dummy_120 D R q) (nb096_wpp_notmem_0290 D R) (nb096_wpp_notmem_0291 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_116 D R) (nb096_alpha_dummy_119 D R q) (nb096_wpp_notmem_0292 D R) (nb096_wpp_notmem_0293 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_115 D R) (nb096_alpha_dummy_118 D R q) (nb096_wpp_notmem_0294 D R) (nb096_wpp_notmem_0295 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_113 D R) (nb096_alpha_dummy_114 D R q) (nb096_wpp_notmem_0296 D R) (nb096_wpp_notmem_0297 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_109 D R) (nb096_alpha_dummy_111 D R q) (nb096_wpp_notmem_0298 D R) (nb096_wpp_notmem_0299 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_110 D R) (nb096_alpha_dummy_112 D R q) (nb096_wpp_notmem_0300 D R) (nb096_wpp_notmem_0301 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_102 D R) (nb096_alpha_dummy_104 D R q) (nb096_wpp_notmem_0302 D R) (nb096_wpp_notmem_0303 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_101 D R) (nb096_alpha_dummy_103 D R q) (nb096_wpp_notmem_0304 D R) (nb096_wpp_notmem_0305 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_107 D R) (nb096_alpha_dummy_108 D R q) (nb096_wpp_notmem_0306 D R) (nb096_wpp_notmem_0307 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_105 D R) (nb096_alpha_dummy_106 D R q) (nb096_wpp_notmem_0308 D R) (nb096_wpp_notmem_0309 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0176 D R) (nb096_wpp_notmem_0177 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0178 D R) (nb096_wpp_notmem_0179 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0046 D R) (nb096_wpp_notmem_0047 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0048 D R) (nb096_wpp_notmem_0049 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0050 D R) (nb096_wpp_notmem_0051 D R q) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb096_wpp_refl_0017 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)), ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)), ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)), ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0018 D R q)

theorem nb096_wpp_notmem_0310 (D : Class) (R : Class) : (nb096_alpha_dummy_113 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_113, fv_syn_cnnc] using (nb096_compact_fv_empty_0078 D R)

theorem nb096_wpp_notmem_0311 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_114 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_114, fv_syn_cnnc] using (nb096_compact_fv_empty_0079 D R q)

theorem nb096_wpp_notmem_0312 (D : Class) (R : Class) : (nb096_alpha_dummy_109 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_109, fv_syn_cnnc] using (nb096_compact_fv_empty_0080 D R)

theorem nb096_wpp_notmem_0313 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_111 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_111, fv_syn_cnnc] using (nb096_compact_fv_empty_0081 D R q)

theorem nb096_wpp_notmem_0314 (D : Class) (R : Class) : (nb096_alpha_dummy_110 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_110, fv_syn_cnnc] using (nb096_compact_fv_empty_0082 D R)

theorem nb096_wpp_notmem_0315 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_112 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_112, fv_syn_cnnc] using (nb096_compact_fv_empty_0083 D R q)

theorem nb096_wpp_notmem_0316 (D : Class) (R : Class) : (nb096_alpha_dummy_102 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_102, fv_syn_cnnc] using (nb096_compact_fv_empty_0084 D R)

theorem nb096_wpp_notmem_0317 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_104 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_104, fv_syn_cnnc] using (nb096_compact_fv_empty_0085 D R q)

theorem nb096_wpp_notmem_0318 (D : Class) (R : Class) : (nb096_alpha_dummy_101 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_101, fv_syn_cnnc] using (nb096_compact_fv_empty_0086 D R)

theorem nb096_wpp_notmem_0319 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_103 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_103, fv_syn_cnnc] using (nb096_compact_fv_empty_0087 D R q)

theorem nb096_wpp_notmem_0320 (D : Class) (R : Class) : (nb096_alpha_dummy_107 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_107, fv_syn_cnnc] using (nb096_compact_fv_empty_0088 D R)

theorem nb096_wpp_notmem_0321 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_108 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_108, fv_syn_cnnc] using (nb096_compact_fv_empty_0089 D R q)

theorem nb096_wpp_notmem_0322 (D : Class) (R : Class) : (nb096_alpha_dummy_105 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_105, fv_syn_cnnc] using (nb096_compact_fv_empty_0090 D R)

theorem nb096_wpp_notmem_0323 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_106 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_106, fv_syn_cnnc] using (nb096_compact_fv_empty_0091 D R q)

theorem nb096_compact_envfresh_0019 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_113 D R) (nb096_alpha_dummy_114 D R q) (nb096_wpp_notmem_0310 D R) (nb096_wpp_notmem_0311 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_109 D R) (nb096_alpha_dummy_111 D R q) (nb096_wpp_notmem_0312 D R) (nb096_wpp_notmem_0313 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_110 D R) (nb096_alpha_dummy_112 D R q) (nb096_wpp_notmem_0314 D R) (nb096_wpp_notmem_0315 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_102 D R) (nb096_alpha_dummy_104 D R q) (nb096_wpp_notmem_0316 D R) (nb096_wpp_notmem_0317 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_101 D R) (nb096_alpha_dummy_103 D R q) (nb096_wpp_notmem_0318 D R) (nb096_wpp_notmem_0319 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_107 D R) (nb096_alpha_dummy_108 D R q) (nb096_wpp_notmem_0320 D R) (nb096_wpp_notmem_0321 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_105 D R) (nb096_alpha_dummy_106 D R q) (nb096_wpp_notmem_0322 D R) (nb096_wpp_notmem_0323 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0204 D R) (nb096_wpp_notmem_0205 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0206 D R) (nb096_wpp_notmem_0207 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0066 D R) (nb096_wpp_notmem_0067 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0068 D R) (nb096_wpp_notmem_0069 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0070 D R) (nb096_wpp_notmem_0071 D R q) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb096_wpp_refl_0018 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0019 D R q)

theorem nb096_compact_fv_empty_0092 (D : Class) (R : Class) : (nb096_alpha_dummy_135 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0324 (D : Class) (R : Class) : (nb096_alpha_dummy_135 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_135, fv_syn_c1c] using (nb096_compact_fv_empty_0092 D R)

theorem nb096_compact_fv_empty_0093 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_136 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0325 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_136 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_136, fv_syn_c1c] using (nb096_compact_fv_empty_0093 D R q)

theorem nb096_compact_fv_empty_0094 (D : Class) (R : Class) : (nb096_alpha_dummy_133 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0326 (D : Class) (R : Class) : (nb096_alpha_dummy_133 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_133, fv_syn_c1c] using (nb096_compact_fv_empty_0094 D R)

theorem nb096_compact_fv_empty_0095 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_134 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0327 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_134 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_134, fv_syn_c1c] using (nb096_compact_fv_empty_0095 D R q)

theorem nb096_compact_fv_empty_0096 (D : Class) (R : Class) : (nb096_alpha_dummy_131 D R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0328 (D : Class) (R : Class) : (nb096_alpha_dummy_131 D R) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_131, fv_syn_c1c] using (nb096_compact_fv_empty_0096 D R)

theorem nb096_compact_fv_empty_0097 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_132 D R q) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb096_wpp_notmem_0329 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_132 D R q) ∉ ((syn_c1c)).fv := by
  simpa only [nb096_alpha_dummy_132, fv_syn_c1c] using (nb096_compact_fv_empty_0097 D R q)

theorem nb096_compact_envfresh_0020 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)), ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)), ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)), ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)), ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_117 D R) (nb096_alpha_dummy_120 D R q) (nb096_wpp_notmem_0270 D R) (nb096_wpp_notmem_0271 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_116 D R) (nb096_alpha_dummy_119 D R q) (nb096_wpp_notmem_0272 D R) (nb096_wpp_notmem_0273 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_115 D R) (nb096_alpha_dummy_118 D R q) (nb096_wpp_notmem_0274 D R) (nb096_wpp_notmem_0275 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_113 D R) (nb096_alpha_dummy_114 D R q) (nb096_wpp_notmem_0276 D R) (nb096_wpp_notmem_0277 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_109 D R) (nb096_alpha_dummy_111 D R q) (nb096_wpp_notmem_0278 D R) (nb096_wpp_notmem_0279 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_110 D R) (nb096_alpha_dummy_112 D R q) (nb096_wpp_notmem_0280 D R) (nb096_wpp_notmem_0281 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_135 D R) (nb096_alpha_dummy_136 D R q) (nb096_wpp_notmem_0324 D R) (nb096_wpp_notmem_0325 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_133 D R) (nb096_alpha_dummy_134 D R q) (nb096_wpp_notmem_0326 D R) (nb096_wpp_notmem_0327 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_102 D R) (nb096_alpha_dummy_104 D R q) (nb096_wpp_notmem_0282 D R) (nb096_wpp_notmem_0283 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_101 D R) (nb096_alpha_dummy_103 D R q) (nb096_wpp_notmem_0284 D R) (nb096_wpp_notmem_0285 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_131 D R) (nb096_alpha_dummy_132 D R q) (nb096_wpp_notmem_0328 D R) (nb096_wpp_notmem_0329 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_105 D R) (nb096_alpha_dummy_106 D R q) (nb096_wpp_notmem_0288 D R) (nb096_wpp_notmem_0289 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0142 D R) (nb096_wpp_notmem_0143 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0144 D R) (nb096_wpp_notmem_0145 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0020 D R) (nb096_wpp_notmem_0021 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0022 D R) (nb096_wpp_notmem_0023 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0024 D R) (nb096_wpp_notmem_0025 D R q) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb096_wpp_refl_0019 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)), ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)), ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)), ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)), ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0020 D R q)

theorem nb096_wpp_notmem_0330 (D : Class) (R : Class) : (nb096_alpha_dummy_135 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_135, fv_syn_c0] using (nb096_compact_fv_empty_0092 D R)

theorem nb096_wpp_notmem_0331 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_136 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_136, fv_syn_c0] using (nb096_compact_fv_empty_0093 D R q)

theorem nb096_wpp_notmem_0332 (D : Class) (R : Class) : (nb096_alpha_dummy_133 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_133, fv_syn_c0] using (nb096_compact_fv_empty_0094 D R)

theorem nb096_wpp_notmem_0333 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_134 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_134, fv_syn_c0] using (nb096_compact_fv_empty_0095 D R q)

theorem nb096_wpp_notmem_0334 (D : Class) (R : Class) : (nb096_alpha_dummy_131 D R) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_131, fv_syn_c0] using (nb096_compact_fv_empty_0096 D R)

theorem nb096_wpp_notmem_0335 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_132 D R q) ∉ ((syn_c0)).fv := by
  simpa only [nb096_alpha_dummy_132, fv_syn_c0] using (nb096_compact_fv_empty_0097 D R q)

theorem nb096_compact_envfresh_0021 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)), ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)), ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)), ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)), ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_117 D R) (nb096_alpha_dummy_120 D R q) (nb096_wpp_notmem_0290 D R) (nb096_wpp_notmem_0291 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_116 D R) (nb096_alpha_dummy_119 D R q) (nb096_wpp_notmem_0292 D R) (nb096_wpp_notmem_0293 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_115 D R) (nb096_alpha_dummy_118 D R q) (nb096_wpp_notmem_0294 D R) (nb096_wpp_notmem_0295 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_113 D R) (nb096_alpha_dummy_114 D R q) (nb096_wpp_notmem_0296 D R) (nb096_wpp_notmem_0297 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_109 D R) (nb096_alpha_dummy_111 D R q) (nb096_wpp_notmem_0298 D R) (nb096_wpp_notmem_0299 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_110 D R) (nb096_alpha_dummy_112 D R q) (nb096_wpp_notmem_0300 D R) (nb096_wpp_notmem_0301 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_135 D R) (nb096_alpha_dummy_136 D R q) (nb096_wpp_notmem_0330 D R) (nb096_wpp_notmem_0331 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_133 D R) (nb096_alpha_dummy_134 D R q) (nb096_wpp_notmem_0332 D R) (nb096_wpp_notmem_0333 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_102 D R) (nb096_alpha_dummy_104 D R q) (nb096_wpp_notmem_0302 D R) (nb096_wpp_notmem_0303 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_101 D R) (nb096_alpha_dummy_103 D R q) (nb096_wpp_notmem_0304 D R) (nb096_wpp_notmem_0305 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_131 D R) (nb096_alpha_dummy_132 D R q) (nb096_wpp_notmem_0334 D R) (nb096_wpp_notmem_0335 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_105 D R) (nb096_alpha_dummy_106 D R q) (nb096_wpp_notmem_0308 D R) (nb096_wpp_notmem_0309 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0176 D R) (nb096_wpp_notmem_0177 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0178 D R) (nb096_wpp_notmem_0179 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0046 D R) (nb096_wpp_notmem_0047 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0048 D R) (nb096_wpp_notmem_0049 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0050 D R) (nb096_wpp_notmem_0051 D R q) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb096_wpp_refl_0020 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)), ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)), ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)), ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)), ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0021 D R q)

theorem nb096_wpp_notmem_0336 (D : Class) (R : Class) : (nb096_alpha_dummy_135 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_135, fv_syn_cnnc] using (nb096_compact_fv_empty_0092 D R)

theorem nb096_wpp_notmem_0337 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_136 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_136, fv_syn_cnnc] using (nb096_compact_fv_empty_0093 D R q)

theorem nb096_wpp_notmem_0338 (D : Class) (R : Class) : (nb096_alpha_dummy_133 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_133, fv_syn_cnnc] using (nb096_compact_fv_empty_0094 D R)

theorem nb096_wpp_notmem_0339 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_134 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_134, fv_syn_cnnc] using (nb096_compact_fv_empty_0095 D R q)

theorem nb096_wpp_notmem_0340 (D : Class) (R : Class) : (nb096_alpha_dummy_131 D R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_131, fv_syn_cnnc] using (nb096_compact_fv_empty_0096 D R)

theorem nb096_wpp_notmem_0341 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_132 D R q) ∉ ((syn_cnnc)).fv := by
  simpa only [nb096_alpha_dummy_132, fv_syn_cnnc] using (nb096_compact_fv_empty_0097 D R q)

theorem nb096_compact_envfresh_0022 (D : Class) (R : Class) (q : Var) : TEnvFresh [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)), ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb096_alpha_dummy_113 D R) (nb096_alpha_dummy_114 D R q) (nb096_wpp_notmem_0310 D R) (nb096_wpp_notmem_0311 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_109 D R) (nb096_alpha_dummy_111 D R q) (nb096_wpp_notmem_0312 D R) (nb096_wpp_notmem_0313 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_110 D R) (nb096_alpha_dummy_112 D R q) (nb096_wpp_notmem_0314 D R) (nb096_wpp_notmem_0315 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_135 D R) (nb096_alpha_dummy_136 D R q) (nb096_wpp_notmem_0336 D R) (nb096_wpp_notmem_0337 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_133 D R) (nb096_alpha_dummy_134 D R q) (nb096_wpp_notmem_0338 D R) (nb096_wpp_notmem_0339 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_102 D R) (nb096_alpha_dummy_104 D R q) (nb096_wpp_notmem_0316 D R) (nb096_wpp_notmem_0317 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_101 D R) (nb096_alpha_dummy_103 D R q) (nb096_wpp_notmem_0318 D R) (nb096_wpp_notmem_0319 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_131 D R) (nb096_alpha_dummy_132 D R q) (nb096_wpp_notmem_0340 D R) (nb096_wpp_notmem_0341 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_105 D R) (nb096_alpha_dummy_106 D R q) (nb096_wpp_notmem_0322 D R) (nb096_wpp_notmem_0323 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0204 D R) (nb096_wpp_notmem_0205 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0206 D R) (nb096_wpp_notmem_0207 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0066 D R) (nb096_wpp_notmem_0067 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0068 D R) (nb096_wpp_notmem_0069 q) (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0070 D R) (nb096_wpp_notmem_0071 D R q) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb096_wpp_refl_0021 (D : Class) (R : Class) (q : Var) : TReflOn [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)), ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)), ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)), ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)), ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)), ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)), ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)), ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)), ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0022 D R q)

theorem nb096_wpp_notmem_0342 (D : Class) (R : Class) : (nb096_alpha_dummy_133 D R) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_133, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0094 D R)

theorem nb096_wpp_notmem_0343 (D : Class) (R : Class) (q : Var) : (nb096_alpha_dummy_134 D R q) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb096_alpha_dummy_134, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb096_compact_fv_empty_0095 D R q)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
