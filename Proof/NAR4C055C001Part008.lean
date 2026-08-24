import NAR4C055C001Part007

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

theorem nb055_compact_envfresh_0010 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_058) (nb055_alpha_dummy_061 x y) (nb055_wpp_notmem_0146) (nb055_wpp_notmem_0147 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_057) (nb055_alpha_dummy_060 x y) (nb055_wpp_notmem_0148) (nb055_wpp_notmem_0149 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_056) (nb055_alpha_dummy_059 x y) (nb055_wpp_notmem_0150) (nb055_wpp_notmem_0151 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_054) (nb055_alpha_dummy_055 x y) (nb055_wpp_notmem_0152) (nb055_wpp_notmem_0153 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_050) (nb055_alpha_dummy_052 x y) (nb055_wpp_notmem_0154) (nb055_wpp_notmem_0155 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_051) (nb055_alpha_dummy_053 x y) (nb055_wpp_notmem_0156) (nb055_wpp_notmem_0157 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_076) (nb055_alpha_dummy_077 x y) (nb055_wpp_notmem_0176) (nb055_wpp_notmem_0177 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_074) (nb055_alpha_dummy_075 x y) (nb055_wpp_notmem_0178) (nb055_wpp_notmem_0179 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_007) (nb055_alpha_dummy_009 x y) (nb055_wpp_notmem_0020) (nb055_wpp_notmem_0021 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_006) (nb055_alpha_dummy_008 x y) (nb055_wpp_notmem_0022) (nb055_wpp_notmem_0023 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_072) (nb055_alpha_dummy_073 x y) (nb055_wpp_notmem_0180) (nb055_wpp_notmem_0181 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_010) (nb055_alpha_dummy_011 x y) (nb055_wpp_notmem_0026) (nb055_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0028) (nb055_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0030) (nb055_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0032) (nb055_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0034) (nb055_wpp_notmem_0035 x y) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb055_wpp_refl_0010 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0010 x y)

theorem nb055_wpp_notmem_0182 : (nb055_alpha_dummy_076) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_076, fv_syn_c0] using (nb055_compact_fv_empty_0054)

theorem nb055_wpp_notmem_0183 (x : Var) (y : Var) : (nb055_alpha_dummy_077 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_077, fv_syn_c0] using (nb055_compact_fv_empty_0055 x y)

theorem nb055_wpp_notmem_0184 : (nb055_alpha_dummy_074) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_074, fv_syn_c0] using (nb055_compact_fv_empty_0056)

theorem nb055_wpp_notmem_0185 (x : Var) (y : Var) : (nb055_alpha_dummy_075 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_075, fv_syn_c0] using (nb055_compact_fv_empty_0057 x y)

theorem nb055_wpp_notmem_0186 : (nb055_alpha_dummy_072) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_072, fv_syn_c0] using (nb055_compact_fv_empty_0058)

theorem nb055_wpp_notmem_0187 (x : Var) (y : Var) : (nb055_alpha_dummy_073 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_073, fv_syn_c0] using (nb055_compact_fv_empty_0059 x y)

theorem nb055_compact_envfresh_0011 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_058) (nb055_alpha_dummy_061 x y) (nb055_wpp_notmem_0158) (nb055_wpp_notmem_0159 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_057) (nb055_alpha_dummy_060 x y) (nb055_wpp_notmem_0160) (nb055_wpp_notmem_0161 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_056) (nb055_alpha_dummy_059 x y) (nb055_wpp_notmem_0162) (nb055_wpp_notmem_0163 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_054) (nb055_alpha_dummy_055 x y) (nb055_wpp_notmem_0164) (nb055_wpp_notmem_0165 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_050) (nb055_alpha_dummy_052 x y) (nb055_wpp_notmem_0166) (nb055_wpp_notmem_0167 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_051) (nb055_alpha_dummy_053 x y) (nb055_wpp_notmem_0168) (nb055_wpp_notmem_0169 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_076) (nb055_alpha_dummy_077 x y) (nb055_wpp_notmem_0182) (nb055_wpp_notmem_0183 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_074) (nb055_alpha_dummy_075 x y) (nb055_wpp_notmem_0184) (nb055_wpp_notmem_0185 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_007) (nb055_alpha_dummy_009 x y) (nb055_wpp_notmem_0056) (nb055_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_006) (nb055_alpha_dummy_008 x y) (nb055_wpp_notmem_0058) (nb055_wpp_notmem_0059 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_072) (nb055_alpha_dummy_073 x y) (nb055_wpp_notmem_0186) (nb055_wpp_notmem_0187 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_010) (nb055_alpha_dummy_011 x y) (nb055_wpp_notmem_0062) (nb055_wpp_notmem_0063 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0064) (nb055_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0066) (nb055_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0068) (nb055_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0070) (nb055_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb055_wpp_refl_0011 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0011 x y)

noncomputable def nb055_split_alpha_0007 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_056)) (syn_cun (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_059 x y)) (syn_cun (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c0) (nb055_wpp_refl_0011 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb055_wpp_notmem_0188 : (nb055_alpha_dummy_076) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_076, fv_syn_cnnc] using (nb055_compact_fv_empty_0054)

theorem nb055_wpp_notmem_0189 (x : Var) (y : Var) : (nb055_alpha_dummy_077 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_077, fv_syn_cnnc] using (nb055_compact_fv_empty_0055 x y)

theorem nb055_wpp_notmem_0190 : (nb055_alpha_dummy_074) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_074, fv_syn_cnnc] using (nb055_compact_fv_empty_0056)

theorem nb055_wpp_notmem_0191 (x : Var) (y : Var) : (nb055_alpha_dummy_075 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_075, fv_syn_cnnc] using (nb055_compact_fv_empty_0057 x y)

theorem nb055_wpp_notmem_0192 : (nb055_alpha_dummy_072) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_072, fv_syn_cnnc] using (nb055_compact_fv_empty_0058)

theorem nb055_wpp_notmem_0193 (x : Var) (y : Var) : (nb055_alpha_dummy_073 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_073, fv_syn_cnnc] using (nb055_compact_fv_empty_0059 x y)

theorem nb055_compact_envfresh_0012 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_054) (nb055_alpha_dummy_055 x y) (nb055_wpp_notmem_0170) (nb055_wpp_notmem_0171 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_050) (nb055_alpha_dummy_052 x y) (nb055_wpp_notmem_0172) (nb055_wpp_notmem_0173 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_051) (nb055_alpha_dummy_053 x y) (nb055_wpp_notmem_0174) (nb055_wpp_notmem_0175 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_076) (nb055_alpha_dummy_077 x y) (nb055_wpp_notmem_0188) (nb055_wpp_notmem_0189 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_074) (nb055_alpha_dummy_075 x y) (nb055_wpp_notmem_0190) (nb055_wpp_notmem_0191 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_007) (nb055_alpha_dummy_009 x y) (nb055_wpp_notmem_0086) (nb055_wpp_notmem_0087 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_006) (nb055_alpha_dummy_008 x y) (nb055_wpp_notmem_0088) (nb055_wpp_notmem_0089 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_072) (nb055_alpha_dummy_073 x y) (nb055_wpp_notmem_0192) (nb055_wpp_notmem_0193 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_010) (nb055_alpha_dummy_011 x y) (nb055_wpp_notmem_0092) (nb055_wpp_notmem_0093 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0094) (nb055_wpp_notmem_0095 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0096) (nb055_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0098) (nb055_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0100) (nb055_wpp_notmem_0101 x y) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb055_wpp_refl_0012 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0012 x y)

noncomputable def nb055_split_alpha_0008 (x : Var) (y : Var) : TAlphaClass [((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Class.cab (nb055_alpha_dummy_051) (syn_wrex (nb055_alpha_dummy_050) (Class.cv (nb055_alpha_dummy_007)) (Wff.classEq (Class.cv (nb055_alpha_dummy_051)) (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc)) (syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c)) (Class.cv (nb055_alpha_dummy_050)))))) (Class.cab (nb055_alpha_dummy_053 x y) (syn_wrex (nb055_alpha_dummy_052 x y) (Class.cv (nb055_alpha_dummy_009 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_053 x y)) (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc)) (syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c)) (Class.cv (nb055_alpha_dummy_052 x y)))))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0091 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0089 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_007))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_009 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0064) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0065 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c1c) (nb055_wpp_refl_0010 x y))) (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0007 x y)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0012 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)), ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0012 x y)))))))))))))))))

theorem nb055_wpp_notmem_0194 : (nb055_alpha_dummy_074) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_074, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0056)

theorem nb055_wpp_notmem_0195 (x : Var) (y : Var) : (nb055_alpha_dummy_075 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_075, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0057 x y)

theorem nb055_wpp_notmem_0196 : (nb055_alpha_dummy_072) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_072, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0058)

theorem nb055_wpp_notmem_0197 (x : Var) (y : Var) : (nb055_alpha_dummy_073 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_073, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0059 x y)

theorem nb055_compact_envfresh_0013 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_074) (nb055_alpha_dummy_075 x y) (nb055_wpp_notmem_0194) (nb055_wpp_notmem_0195 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_007) (nb055_alpha_dummy_009 x y) (nb055_wpp_notmem_0130) (nb055_wpp_notmem_0131 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_006) (nb055_alpha_dummy_008 x y) (nb055_wpp_notmem_0132) (nb055_wpp_notmem_0133 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_072) (nb055_alpha_dummy_073 x y) (nb055_wpp_notmem_0196) (nb055_wpp_notmem_0197 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_010) (nb055_alpha_dummy_011 x y) (nb055_wpp_notmem_0136) (nb055_wpp_notmem_0137 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0138) (nb055_wpp_notmem_0139 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0140) (nb055_wpp_notmem_0141 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0142) (nb055_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0144) (nb055_wpp_notmem_0145 x y) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))

noncomputable def nb055_wpp_refl_0013 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0013 x y)

noncomputable def nb055_split_alpha_0009 (x : Var) (y : Var) (dv_x_y : x ≠ y) : TAlphaWff [((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_010)) (syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))) (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_010)) (syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c)))))))))) (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_011 x y)) (syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))) (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_011 x y)) (syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0006 x y dv_x_y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0006 x y dv_x_y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0087 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0083) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0085 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb055_split_alpha_0008 x y)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb055_split_alpha_0008 x y)))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_ccompl (syn_csn (syn_c0c))) (nb055_wpp_refl_0013 x y))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0087 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0083) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0085 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb055_split_alpha_0008 x y)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb055_split_alpha_0008 x y)))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_ccompl (syn_csn (syn_c0c))) (nb055_wpp_refl_0013 x y)))))))))))))))))))))))))

theorem nb055_wpp_notmem_0198 : (nb055_alpha_dummy_002) ∉ ((syn_cvv)).fv := by
  simpa only [nb055_alpha_dummy_002, fv_syn_cvv] using (nb055_compact_fv_empty_0028)

theorem nb055_wpp_notmem_0199 (x : Var) (y : Var) : (nb055_alpha_dummy_003 x y) ∉ ((syn_cvv)).fv := by
  simpa only [nb055_alpha_dummy_003, fv_syn_cvv] using (nb055_compact_fv_empty_0029 x y)

theorem nb055_wpp_notmem_0200 : (nb055_alpha_dummy_001) ∉ ((syn_cvv)).fv := by
  simpa only [nb055_alpha_dummy_001, fv_syn_cvv] using (nb055_compact_fv_empty_0030)

theorem nb055_wpp_notmem_0201 (y : Var) : y ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb055_compact_fv_empty_0031 y)

theorem nb055_wpp_notmem_0202 : (nb055_alpha_dummy_000) ∉ ((syn_cvv)).fv := by
  simpa only [nb055_alpha_dummy_000, fv_syn_cvv] using (nb055_compact_fv_empty_0032)

theorem nb055_wpp_notmem_0203 (x : Var) : x ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb055_compact_fv_empty_0033 x)

theorem nb055_wpp_notmem_0204 : (nb055_alpha_dummy_004) ∉ ((syn_cvv)).fv := by
  simpa only [nb055_alpha_dummy_004, fv_syn_cvv] using (nb055_compact_fv_empty_0034)

theorem nb055_wpp_notmem_0205 (x : Var) (y : Var) : (nb055_alpha_dummy_005 x y) ∉ ((syn_cvv)).fv := by
  simpa only [nb055_alpha_dummy_005, fv_syn_cvv] using (nb055_compact_fv_empty_0035 x y)

theorem nb055_compact_envfresh_0014 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0198) (nb055_wpp_notmem_0199 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0200) (nb055_wpp_notmem_0201 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0202) (nb055_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0204) (nb055_wpp_notmem_0205 x y) (TEnvFresh.nil ((syn_cvv)).fv)))))

noncomputable def nb055_wpp_refl_0014 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0014 x y)

theorem nb055_compact_fv_empty_0060 : (nb055_alpha_dummy_098) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0206 : (nb055_alpha_dummy_098) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_098, fv_syn_c1c] using (nb055_compact_fv_empty_0060)

theorem nb055_compact_fv_empty_0061 (x : Var) (y : Var) : (nb055_alpha_dummy_101 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0207 (x : Var) (y : Var) : (nb055_alpha_dummy_101 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_101, fv_syn_c1c] using (nb055_compact_fv_empty_0061 x y)

theorem nb055_compact_fv_empty_0062 : (nb055_alpha_dummy_097) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0208 : (nb055_alpha_dummy_097) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_097, fv_syn_c1c] using (nb055_compact_fv_empty_0062)

theorem nb055_compact_fv_empty_0063 (x : Var) (y : Var) : (nb055_alpha_dummy_100 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0209 (x : Var) (y : Var) : (nb055_alpha_dummy_100 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_100, fv_syn_c1c] using (nb055_compact_fv_empty_0063 x y)

theorem nb055_compact_fv_empty_0064 : (nb055_alpha_dummy_096) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0210 : (nb055_alpha_dummy_096) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_096, fv_syn_c1c] using (nb055_compact_fv_empty_0064)

theorem nb055_compact_fv_empty_0065 (x : Var) (y : Var) : (nb055_alpha_dummy_099 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0211 (x : Var) (y : Var) : (nb055_alpha_dummy_099 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_099, fv_syn_c1c] using (nb055_compact_fv_empty_0065 x y)

theorem nb055_compact_fv_empty_0066 : (nb055_alpha_dummy_094) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0212 : (nb055_alpha_dummy_094) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_094, fv_syn_c1c] using (nb055_compact_fv_empty_0066)

theorem nb055_compact_fv_empty_0067 (x : Var) (y : Var) : (nb055_alpha_dummy_095 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0213 (x : Var) (y : Var) : (nb055_alpha_dummy_095 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_095, fv_syn_c1c] using (nb055_compact_fv_empty_0067 x y)

theorem nb055_compact_fv_empty_0068 : (nb055_alpha_dummy_090) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0214 : (nb055_alpha_dummy_090) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_090, fv_syn_c1c] using (nb055_compact_fv_empty_0068)

theorem nb055_compact_fv_empty_0069 (x : Var) (y : Var) : (nb055_alpha_dummy_092 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0215 (x : Var) (y : Var) : (nb055_alpha_dummy_092 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_092, fv_syn_c1c] using (nb055_compact_fv_empty_0069 x y)

theorem nb055_compact_fv_empty_0070 : (nb055_alpha_dummy_091) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0216 : (nb055_alpha_dummy_091) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_091, fv_syn_c1c] using (nb055_compact_fv_empty_0070)

theorem nb055_compact_fv_empty_0071 (x : Var) (y : Var) : (nb055_alpha_dummy_093 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0217 (x : Var) (y : Var) : (nb055_alpha_dummy_093 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_093, fv_syn_c1c] using (nb055_compact_fv_empty_0071 x y)

theorem nb055_compact_fv_empty_0072 : (nb055_alpha_dummy_083) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0218 : (nb055_alpha_dummy_083) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_083, fv_syn_c1c] using (nb055_compact_fv_empty_0072)

theorem nb055_compact_fv_empty_0073 (x : Var) (y : Var) : (nb055_alpha_dummy_085 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0219 (x : Var) (y : Var) : (nb055_alpha_dummy_085 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_085, fv_syn_c1c] using (nb055_compact_fv_empty_0073 x y)

theorem nb055_compact_fv_empty_0074 : (nb055_alpha_dummy_082) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0220 : (nb055_alpha_dummy_082) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_082, fv_syn_c1c] using (nb055_compact_fv_empty_0074)

theorem nb055_compact_fv_empty_0075 (x : Var) (y : Var) : (nb055_alpha_dummy_084 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0221 (x : Var) (y : Var) : (nb055_alpha_dummy_084 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_084, fv_syn_c1c] using (nb055_compact_fv_empty_0075 x y)

theorem nb055_compact_fv_empty_0076 : (nb055_alpha_dummy_088) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0222 : (nb055_alpha_dummy_088) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_088, fv_syn_c1c] using (nb055_compact_fv_empty_0076)

theorem nb055_compact_fv_empty_0077 (x : Var) (y : Var) : (nb055_alpha_dummy_089 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0223 (x : Var) (y : Var) : (nb055_alpha_dummy_089 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_089, fv_syn_c1c] using (nb055_compact_fv_empty_0077 x y)

theorem nb055_compact_fv_empty_0078 : (nb055_alpha_dummy_086) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0224 : (nb055_alpha_dummy_086) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_086, fv_syn_c1c] using (nb055_compact_fv_empty_0078)

theorem nb055_compact_fv_empty_0079 (x : Var) (y : Var) : (nb055_alpha_dummy_087 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0225 (x : Var) (y : Var) : (nb055_alpha_dummy_087 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_087, fv_syn_c1c] using (nb055_compact_fv_empty_0079 x y)

theorem nb055_compact_fv_empty_0080 : (nb055_alpha_dummy_080) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0226 : (nb055_alpha_dummy_080) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_080, fv_syn_c1c] using (nb055_compact_fv_empty_0080)

theorem nb055_compact_fv_empty_0081 (x : Var) (y : Var) : (nb055_alpha_dummy_081 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0227 (x : Var) (y : Var) : (nb055_alpha_dummy_081 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_081, fv_syn_c1c] using (nb055_compact_fv_empty_0081 x y)

theorem nb055_compact_envfresh_0015 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_098), (nb055_alpha_dummy_101 x y)), ((nb055_alpha_dummy_097), (nb055_alpha_dummy_100 x y)), ((nb055_alpha_dummy_096), (nb055_alpha_dummy_099 x y)), ((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)), ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)), ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)), ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)), ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)), ((nb055_alpha_dummy_088), (nb055_alpha_dummy_089 x y)), ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_098) (nb055_alpha_dummy_101 x y) (nb055_wpp_notmem_0206) (nb055_wpp_notmem_0207 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_097) (nb055_alpha_dummy_100 x y) (nb055_wpp_notmem_0208) (nb055_wpp_notmem_0209 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_096) (nb055_alpha_dummy_099 x y) (nb055_wpp_notmem_0210) (nb055_wpp_notmem_0211 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_094) (nb055_alpha_dummy_095 x y) (nb055_wpp_notmem_0212) (nb055_wpp_notmem_0213 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_090) (nb055_alpha_dummy_092 x y) (nb055_wpp_notmem_0214) (nb055_wpp_notmem_0215 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_091) (nb055_alpha_dummy_093 x y) (nb055_wpp_notmem_0216) (nb055_wpp_notmem_0217 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_083) (nb055_alpha_dummy_085 x y) (nb055_wpp_notmem_0218) (nb055_wpp_notmem_0219 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_082) (nb055_alpha_dummy_084 x y) (nb055_wpp_notmem_0220) (nb055_wpp_notmem_0221 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_088) (nb055_alpha_dummy_089 x y) (nb055_wpp_notmem_0222) (nb055_wpp_notmem_0223 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_086) (nb055_alpha_dummy_087 x y) (nb055_wpp_notmem_0224) (nb055_wpp_notmem_0225 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0012) (nb055_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0014) (nb055_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0226) (nb055_wpp_notmem_0227 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0028) (nb055_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0030) (nb055_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0032) (nb055_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0034) (nb055_wpp_notmem_0035 x y) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb055_wpp_refl_0015 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_098), (nb055_alpha_dummy_101 x y)), ((nb055_alpha_dummy_097), (nb055_alpha_dummy_100 x y)), ((nb055_alpha_dummy_096), (nb055_alpha_dummy_099 x y)), ((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)), ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)), ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)), ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)), ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)), ((nb055_alpha_dummy_088), (nb055_alpha_dummy_089 x y)), ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0015 x y)

theorem nb055_wpp_notmem_0228 : (nb055_alpha_dummy_098) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_098, fv_syn_c0] using (nb055_compact_fv_empty_0060)

theorem nb055_wpp_notmem_0229 (x : Var) (y : Var) : (nb055_alpha_dummy_101 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_101, fv_syn_c0] using (nb055_compact_fv_empty_0061 x y)

theorem nb055_wpp_notmem_0230 : (nb055_alpha_dummy_097) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_097, fv_syn_c0] using (nb055_compact_fv_empty_0062)

theorem nb055_wpp_notmem_0231 (x : Var) (y : Var) : (nb055_alpha_dummy_100 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_100, fv_syn_c0] using (nb055_compact_fv_empty_0063 x y)

theorem nb055_wpp_notmem_0232 : (nb055_alpha_dummy_096) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_096, fv_syn_c0] using (nb055_compact_fv_empty_0064)

theorem nb055_wpp_notmem_0233 (x : Var) (y : Var) : (nb055_alpha_dummy_099 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_099, fv_syn_c0] using (nb055_compact_fv_empty_0065 x y)

theorem nb055_wpp_notmem_0234 : (nb055_alpha_dummy_094) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_094, fv_syn_c0] using (nb055_compact_fv_empty_0066)

theorem nb055_wpp_notmem_0235 (x : Var) (y : Var) : (nb055_alpha_dummy_095 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_095, fv_syn_c0] using (nb055_compact_fv_empty_0067 x y)

theorem nb055_wpp_notmem_0236 : (nb055_alpha_dummy_090) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_090, fv_syn_c0] using (nb055_compact_fv_empty_0068)

theorem nb055_wpp_notmem_0237 (x : Var) (y : Var) : (nb055_alpha_dummy_092 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_092, fv_syn_c0] using (nb055_compact_fv_empty_0069 x y)

theorem nb055_wpp_notmem_0238 : (nb055_alpha_dummy_091) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_091, fv_syn_c0] using (nb055_compact_fv_empty_0070)

theorem nb055_wpp_notmem_0239 (x : Var) (y : Var) : (nb055_alpha_dummy_093 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_093, fv_syn_c0] using (nb055_compact_fv_empty_0071 x y)

theorem nb055_wpp_notmem_0240 : (nb055_alpha_dummy_083) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_083, fv_syn_c0] using (nb055_compact_fv_empty_0072)

theorem nb055_wpp_notmem_0241 (x : Var) (y : Var) : (nb055_alpha_dummy_085 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_085, fv_syn_c0] using (nb055_compact_fv_empty_0073 x y)

theorem nb055_wpp_notmem_0242 : (nb055_alpha_dummy_082) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_082, fv_syn_c0] using (nb055_compact_fv_empty_0074)

theorem nb055_wpp_notmem_0243 (x : Var) (y : Var) : (nb055_alpha_dummy_084 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_084, fv_syn_c0] using (nb055_compact_fv_empty_0075 x y)

theorem nb055_wpp_notmem_0244 : (nb055_alpha_dummy_088) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_088, fv_syn_c0] using (nb055_compact_fv_empty_0076)

theorem nb055_wpp_notmem_0245 (x : Var) (y : Var) : (nb055_alpha_dummy_089 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_089, fv_syn_c0] using (nb055_compact_fv_empty_0077 x y)

theorem nb055_wpp_notmem_0246 : (nb055_alpha_dummy_086) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_086, fv_syn_c0] using (nb055_compact_fv_empty_0078)

theorem nb055_wpp_notmem_0247 (x : Var) (y : Var) : (nb055_alpha_dummy_087 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_087, fv_syn_c0] using (nb055_compact_fv_empty_0079 x y)

theorem nb055_wpp_notmem_0248 : (nb055_alpha_dummy_080) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_080, fv_syn_c0] using (nb055_compact_fv_empty_0080)

theorem nb055_wpp_notmem_0249 (x : Var) (y : Var) : (nb055_alpha_dummy_081 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_081, fv_syn_c0] using (nb055_compact_fv_empty_0081 x y)

theorem nb055_compact_envfresh_0016 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_098), (nb055_alpha_dummy_101 x y)), ((nb055_alpha_dummy_097), (nb055_alpha_dummy_100 x y)), ((nb055_alpha_dummy_096), (nb055_alpha_dummy_099 x y)), ((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)), ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)), ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)), ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)), ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)), ((nb055_alpha_dummy_088), (nb055_alpha_dummy_089 x y)), ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_098) (nb055_alpha_dummy_101 x y) (nb055_wpp_notmem_0228) (nb055_wpp_notmem_0229 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_097) (nb055_alpha_dummy_100 x y) (nb055_wpp_notmem_0230) (nb055_wpp_notmem_0231 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_096) (nb055_alpha_dummy_099 x y) (nb055_wpp_notmem_0232) (nb055_wpp_notmem_0233 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_094) (nb055_alpha_dummy_095 x y) (nb055_wpp_notmem_0234) (nb055_wpp_notmem_0235 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_090) (nb055_alpha_dummy_092 x y) (nb055_wpp_notmem_0236) (nb055_wpp_notmem_0237 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_091) (nb055_alpha_dummy_093 x y) (nb055_wpp_notmem_0238) (nb055_wpp_notmem_0239 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_083) (nb055_alpha_dummy_085 x y) (nb055_wpp_notmem_0240) (nb055_wpp_notmem_0241 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_082) (nb055_alpha_dummy_084 x y) (nb055_wpp_notmem_0242) (nb055_wpp_notmem_0243 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_088) (nb055_alpha_dummy_089 x y) (nb055_wpp_notmem_0244) (nb055_wpp_notmem_0245 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_086) (nb055_alpha_dummy_087 x y) (nb055_wpp_notmem_0246) (nb055_wpp_notmem_0247 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0048) (nb055_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0050) (nb055_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_080) (nb055_alpha_dummy_081 x y) (nb055_wpp_notmem_0248) (nb055_wpp_notmem_0249 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0064) (nb055_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0066) (nb055_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0068) (nb055_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0070) (nb055_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb055_wpp_refl_0016 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_098), (nb055_alpha_dummy_101 x y)), ((nb055_alpha_dummy_097), (nb055_alpha_dummy_100 x y)), ((nb055_alpha_dummy_096), (nb055_alpha_dummy_099 x y)), ((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)), ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)), ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)), ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)), ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)), ((nb055_alpha_dummy_088), (nb055_alpha_dummy_089 x y)), ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0016 x y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
