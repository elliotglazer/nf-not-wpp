import NAR4C067C001Part011

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

theorem nb067_wpp_notmem_0178 : (nb067_alpha_dummy_075) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_075, fv_syn_c1c] using (nb067_compact_fv_empty_0056)

theorem nb067_compact_fv_empty_0057 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_076 x y f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0179 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_076 x y f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_076, fv_syn_c1c] using (nb067_compact_fv_empty_0057 x y f)

theorem nb067_compact_fv_empty_0058 : (nb067_alpha_dummy_073) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0180 : (nb067_alpha_dummy_073) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_073, fv_syn_c1c] using (nb067_compact_fv_empty_0058)

theorem nb067_compact_fv_empty_0059 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_074 x y f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0181 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_074 x y f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_074, fv_syn_c1c] using (nb067_compact_fv_empty_0059 x y f)

theorem nb067_compact_envfresh_0010 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)), ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)), ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)), ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_059) (nb067_alpha_dummy_062 x y f) (nb067_wpp_notmem_0146) (nb067_wpp_notmem_0147 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_058) (nb067_alpha_dummy_061 x y f) (nb067_wpp_notmem_0148) (nb067_wpp_notmem_0149 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_057) (nb067_alpha_dummy_060 x y f) (nb067_wpp_notmem_0150) (nb067_wpp_notmem_0151 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_055) (nb067_alpha_dummy_056 x y f) (nb067_wpp_notmem_0152) (nb067_wpp_notmem_0153 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_051) (nb067_alpha_dummy_053 x y f) (nb067_wpp_notmem_0154) (nb067_wpp_notmem_0155 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_052) (nb067_alpha_dummy_054 x y f) (nb067_wpp_notmem_0156) (nb067_wpp_notmem_0157 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_077) (nb067_alpha_dummy_078 x y f) (nb067_wpp_notmem_0176) (nb067_wpp_notmem_0177 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_075) (nb067_alpha_dummy_076 x y f) (nb067_wpp_notmem_0178) (nb067_wpp_notmem_0179 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0020) (nb067_wpp_notmem_0021 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0022) (nb067_wpp_notmem_0023 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_073) (nb067_alpha_dummy_074 x y f) (nb067_wpp_notmem_0180) (nb067_wpp_notmem_0181 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0026) (nb067_wpp_notmem_0027 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb067_wpp_refl_0010 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)), ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)), ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)), ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0010 x y f)

theorem nb067_wpp_notmem_0182 : (nb067_alpha_dummy_077) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_077, fv_syn_c0] using (nb067_compact_fv_empty_0054)

theorem nb067_wpp_notmem_0183 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_078 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_078, fv_syn_c0] using (nb067_compact_fv_empty_0055 x y f)

theorem nb067_wpp_notmem_0184 : (nb067_alpha_dummy_075) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_075, fv_syn_c0] using (nb067_compact_fv_empty_0056)

theorem nb067_wpp_notmem_0185 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_076 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_076, fv_syn_c0] using (nb067_compact_fv_empty_0057 x y f)

theorem nb067_wpp_notmem_0186 : (nb067_alpha_dummy_073) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_073, fv_syn_c0] using (nb067_compact_fv_empty_0058)

theorem nb067_wpp_notmem_0187 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_074 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_074, fv_syn_c0] using (nb067_compact_fv_empty_0059 x y f)

theorem nb067_compact_envfresh_0011 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)), ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)), ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)), ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_059) (nb067_alpha_dummy_062 x y f) (nb067_wpp_notmem_0158) (nb067_wpp_notmem_0159 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_058) (nb067_alpha_dummy_061 x y f) (nb067_wpp_notmem_0160) (nb067_wpp_notmem_0161 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_057) (nb067_alpha_dummy_060 x y f) (nb067_wpp_notmem_0162) (nb067_wpp_notmem_0163 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_055) (nb067_alpha_dummy_056 x y f) (nb067_wpp_notmem_0164) (nb067_wpp_notmem_0165 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_051) (nb067_alpha_dummy_053 x y f) (nb067_wpp_notmem_0166) (nb067_wpp_notmem_0167 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_052) (nb067_alpha_dummy_054 x y f) (nb067_wpp_notmem_0168) (nb067_wpp_notmem_0169 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_077) (nb067_alpha_dummy_078 x y f) (nb067_wpp_notmem_0182) (nb067_wpp_notmem_0183 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_075) (nb067_alpha_dummy_076 x y f) (nb067_wpp_notmem_0184) (nb067_wpp_notmem_0185 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0056) (nb067_wpp_notmem_0057 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0058) (nb067_wpp_notmem_0059 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_073) (nb067_alpha_dummy_074 x y f) (nb067_wpp_notmem_0186) (nb067_wpp_notmem_0187 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0062) (nb067_wpp_notmem_0063 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0064) (nb067_wpp_notmem_0065 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0066) (nb067_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0068) (nb067_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0070) (nb067_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb067_wpp_refl_0011 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)), ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)), ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)), ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0011 x y f)

noncomputable def nb067_split_alpha_0007 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)), ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)), ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)), ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_057)) (syn_cun (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_060 x y f)) (syn_cun (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)), ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)), ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)), ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c0) (nb067_wpp_refl_0011 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb067_wpp_notmem_0188 : (nb067_alpha_dummy_077) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_077, fv_syn_cnnc] using (nb067_compact_fv_empty_0054)

theorem nb067_wpp_notmem_0189 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_078 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_078, fv_syn_cnnc] using (nb067_compact_fv_empty_0055 x y f)

theorem nb067_wpp_notmem_0190 : (nb067_alpha_dummy_075) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_075, fv_syn_cnnc] using (nb067_compact_fv_empty_0056)

theorem nb067_wpp_notmem_0191 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_076 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_076, fv_syn_cnnc] using (nb067_compact_fv_empty_0057 x y f)

theorem nb067_wpp_notmem_0192 : (nb067_alpha_dummy_073) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_073, fv_syn_cnnc] using (nb067_compact_fv_empty_0058)

theorem nb067_wpp_notmem_0193 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_074 x y f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_074, fv_syn_cnnc] using (nb067_compact_fv_empty_0059 x y f)

theorem nb067_compact_envfresh_0012 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_055) (nb067_alpha_dummy_056 x y f) (nb067_wpp_notmem_0170) (nb067_wpp_notmem_0171 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_051) (nb067_alpha_dummy_053 x y f) (nb067_wpp_notmem_0172) (nb067_wpp_notmem_0173 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_052) (nb067_alpha_dummy_054 x y f) (nb067_wpp_notmem_0174) (nb067_wpp_notmem_0175 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_077) (nb067_alpha_dummy_078 x y f) (nb067_wpp_notmem_0188) (nb067_wpp_notmem_0189 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_075) (nb067_alpha_dummy_076 x y f) (nb067_wpp_notmem_0190) (nb067_wpp_notmem_0191 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0086) (nb067_wpp_notmem_0087 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0088) (nb067_wpp_notmem_0089 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_073) (nb067_alpha_dummy_074 x y f) (nb067_wpp_notmem_0192) (nb067_wpp_notmem_0193 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0092) (nb067_wpp_notmem_0093 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0094) (nb067_wpp_notmem_0095 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0096) (nb067_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0098) (nb067_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0100) (nb067_wpp_notmem_0101 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb067_wpp_refl_0012 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0012 x y f)

noncomputable def nb067_split_alpha_0008 (x : Var) (y : Var) (f : Var) : TAlphaClass [((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Class.cab (nb067_alpha_dummy_052) (syn_wrex (nb067_alpha_dummy_051) (Class.cv (nb067_alpha_dummy_008)) (Wff.classEq (Class.cv (nb067_alpha_dummy_052)) (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc)) (syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c)) (Class.cv (nb067_alpha_dummy_051)))))) (Class.cab (nb067_alpha_dummy_054 x y f) (syn_wrex (nb067_alpha_dummy_053 x y f) (Class.cv (nb067_alpha_dummy_010 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_054 x y f)) (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc)) (syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c)) (Class.cv (nb067_alpha_dummy_053 x y f)))))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0091 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0089 x y f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_008))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0064) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0065 x y f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0065 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)), ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)), ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)), ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c1c) (nb067_wpp_refl_0010 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0007 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0012 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0012 x y f)))))))))))))))))

theorem nb067_wpp_notmem_0194 : (nb067_alpha_dummy_075) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_075, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0056)

theorem nb067_wpp_notmem_0195 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_076 x y f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_076, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0057 x y f)

theorem nb067_wpp_notmem_0196 : (nb067_alpha_dummy_073) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_073, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0058)

theorem nb067_wpp_notmem_0197 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_074 x y f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb067_alpha_dummy_074, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb067_compact_fv_empty_0059 x y f)

theorem nb067_compact_envfresh_0013 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_075) (nb067_alpha_dummy_076 x y f) (nb067_wpp_notmem_0194) (nb067_wpp_notmem_0195 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0130) (nb067_wpp_notmem_0131 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0132) (nb067_wpp_notmem_0133 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_073) (nb067_alpha_dummy_074 x y f) (nb067_wpp_notmem_0196) (nb067_wpp_notmem_0197 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0136) (nb067_wpp_notmem_0137 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0138) (nb067_wpp_notmem_0139 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0140) (nb067_wpp_notmem_0141 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0142) (nb067_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0144) (nb067_wpp_notmem_0145 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))

noncomputable def nb067_wpp_refl_0013 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0013 x y f)

noncomputable def nb067_split_alpha_0009 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) : TAlphaWff [((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_011)) (syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))) (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_011)) (syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c)))))))))) (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_012 x y f)) (syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))) (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_012 x y f)) (syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0006 x y f dv_x_y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0006 x y f dv_x_y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0087 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0083) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0085 x y f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) (by decide)) (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb067_split_alpha_0008 x y f)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb067_split_alpha_0008 x y f)))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb067_wpp_refl_0013 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0087 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0083) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0085 x y f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) (by decide)) (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb067_split_alpha_0008 x y f)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb067_split_alpha_0008 x y f)))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb067_wpp_refl_0013 x y f)))))))))))))))))))))))))

theorem nb067_wpp_notmem_0198 : (nb067_alpha_dummy_003) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_003, fv_syn_cvv] using (nb067_compact_fv_empty_0028)

theorem nb067_wpp_notmem_0199 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_004, fv_syn_cvv] using (nb067_compact_fv_empty_0029 x y f)

theorem nb067_wpp_notmem_0200 : (nb067_alpha_dummy_002) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_002, fv_syn_cvv] using (nb067_compact_fv_empty_0030)

theorem nb067_wpp_notmem_0201 (y : Var) : y ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb067_compact_fv_empty_0031 y)

theorem nb067_wpp_notmem_0202 : (nb067_alpha_dummy_001) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_001, fv_syn_cvv] using (nb067_compact_fv_empty_0032)

theorem nb067_wpp_notmem_0203 (x : Var) : x ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb067_compact_fv_empty_0033 x)

theorem nb067_wpp_notmem_0204 : (nb067_alpha_dummy_005) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_005, fv_syn_cvv] using (nb067_compact_fv_empty_0034)

theorem nb067_wpp_notmem_0205 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_006 x y f) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_006, fv_syn_cvv] using (nb067_compact_fv_empty_0035 x y f)

theorem nb067_compact_envfresh_0014 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0198) (nb067_wpp_notmem_0199 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0200) (nb067_wpp_notmem_0201 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0202) (nb067_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0204) (nb067_wpp_notmem_0205 x y f) (TEnvFresh.nil ((syn_cvv)).fv)))))

noncomputable def nb067_wpp_refl_0014 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0014 x y f)

theorem nb067_compact_fv_empty_0060 : (nb067_alpha_dummy_107) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0206 : (nb067_alpha_dummy_107) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_107, fv_syn_c1c] using (nb067_compact_fv_empty_0060)

theorem nb067_compact_fv_empty_0061 (f : Var) : (nb067_alpha_dummy_110 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0207 (f : Var) : (nb067_alpha_dummy_110 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_110, fv_syn_c1c] using (nb067_compact_fv_empty_0061 f)

theorem nb067_compact_fv_empty_0062 : (nb067_alpha_dummy_106) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0208 : (nb067_alpha_dummy_106) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_106, fv_syn_c1c] using (nb067_compact_fv_empty_0062)

theorem nb067_compact_fv_empty_0063 (f : Var) : (nb067_alpha_dummy_109 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0209 (f : Var) : (nb067_alpha_dummy_109 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_109, fv_syn_c1c] using (nb067_compact_fv_empty_0063 f)

theorem nb067_compact_fv_empty_0064 : (nb067_alpha_dummy_105) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0210 : (nb067_alpha_dummy_105) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_105, fv_syn_c1c] using (nb067_compact_fv_empty_0064)

theorem nb067_compact_fv_empty_0065 (f : Var) : (nb067_alpha_dummy_108 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0211 (f : Var) : (nb067_alpha_dummy_108 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_108, fv_syn_c1c] using (nb067_compact_fv_empty_0065 f)

theorem nb067_compact_fv_empty_0066 : (nb067_alpha_dummy_103) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0212 : (nb067_alpha_dummy_103) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_103, fv_syn_c1c] using (nb067_compact_fv_empty_0066)

theorem nb067_compact_fv_empty_0067 (f : Var) : (nb067_alpha_dummy_104 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0213 (f : Var) : (nb067_alpha_dummy_104 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_104, fv_syn_c1c] using (nb067_compact_fv_empty_0067 f)

theorem nb067_compact_fv_empty_0068 : (nb067_alpha_dummy_099) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0214 : (nb067_alpha_dummy_099) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_099, fv_syn_c1c] using (nb067_compact_fv_empty_0068)

theorem nb067_compact_fv_empty_0069 (f : Var) : (nb067_alpha_dummy_101 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0215 (f : Var) : (nb067_alpha_dummy_101 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_101, fv_syn_c1c] using (nb067_compact_fv_empty_0069 f)

theorem nb067_compact_fv_empty_0070 : (nb067_alpha_dummy_100) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0216 : (nb067_alpha_dummy_100) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_100, fv_syn_c1c] using (nb067_compact_fv_empty_0070)

theorem nb067_compact_fv_empty_0071 (f : Var) : (nb067_alpha_dummy_102 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0217 (f : Var) : (nb067_alpha_dummy_102 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_102, fv_syn_c1c] using (nb067_compact_fv_empty_0071 f)

theorem nb067_compact_fv_empty_0072 : (nb067_alpha_dummy_092) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0218 : (nb067_alpha_dummy_092) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_092, fv_syn_c1c] using (nb067_compact_fv_empty_0072)

theorem nb067_compact_fv_empty_0073 (f : Var) : (nb067_alpha_dummy_094 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0219 (f : Var) : (nb067_alpha_dummy_094 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_094, fv_syn_c1c] using (nb067_compact_fv_empty_0073 f)

theorem nb067_compact_fv_empty_0074 : (nb067_alpha_dummy_091) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0220 : (nb067_alpha_dummy_091) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_091, fv_syn_c1c] using (nb067_compact_fv_empty_0074)

theorem nb067_compact_fv_empty_0075 (f : Var) : (nb067_alpha_dummy_093 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0221 (f : Var) : (nb067_alpha_dummy_093 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_093, fv_syn_c1c] using (nb067_compact_fv_empty_0075 f)

theorem nb067_compact_fv_empty_0076 : (nb067_alpha_dummy_097) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0222 : (nb067_alpha_dummy_097) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_097, fv_syn_c1c] using (nb067_compact_fv_empty_0076)

theorem nb067_compact_fv_empty_0077 (f : Var) : (nb067_alpha_dummy_098 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0223 (f : Var) : (nb067_alpha_dummy_098 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_098, fv_syn_c1c] using (nb067_compact_fv_empty_0077 f)

theorem nb067_compact_fv_empty_0078 : (nb067_alpha_dummy_095) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0224 : (nb067_alpha_dummy_095) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_095, fv_syn_c1c] using (nb067_compact_fv_empty_0078)

theorem nb067_compact_fv_empty_0079 (f : Var) : (nb067_alpha_dummy_096 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0225 (f : Var) : (nb067_alpha_dummy_096 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_096, fv_syn_c1c] using (nb067_compact_fv_empty_0079 f)

theorem nb067_compact_fv_empty_0080 : (nb067_alpha_dummy_084) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0226 : (nb067_alpha_dummy_084) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_084, fv_syn_c1c] using (nb067_compact_fv_empty_0080)

theorem nb067_compact_fv_empty_0081 (f : Var) : (nb067_alpha_dummy_087 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0227 (f : Var) : (nb067_alpha_dummy_087 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_087, fv_syn_c1c] using (nb067_compact_fv_empty_0081 f)

theorem nb067_compact_fv_empty_0082 : (nb067_alpha_dummy_083) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0228 : (nb067_alpha_dummy_083) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_083, fv_syn_c1c] using (nb067_compact_fv_empty_0082)

theorem nb067_compact_fv_empty_0083 (f : Var) : (nb067_alpha_dummy_086 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0229 (f : Var) : (nb067_alpha_dummy_086 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_086, fv_syn_c1c] using (nb067_compact_fv_empty_0083 f)

theorem nb067_compact_fv_empty_0084 : (nb067_alpha_dummy_089) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0230 : (nb067_alpha_dummy_089) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_089, fv_syn_c1c] using (nb067_compact_fv_empty_0084)

theorem nb067_compact_fv_empty_0085 (f : Var) : (nb067_alpha_dummy_090 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0231 (f : Var) : (nb067_alpha_dummy_090 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_090, fv_syn_c1c] using (nb067_compact_fv_empty_0085 f)

theorem nb067_compact_fv_empty_0086 : (nb067_alpha_dummy_081) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0232 : (nb067_alpha_dummy_081) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_081, fv_syn_c1c] using (nb067_compact_fv_empty_0086)

theorem nb067_compact_fv_empty_0087 (f : Var) : (nb067_alpha_dummy_082 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0233 (f : Var) : (nb067_alpha_dummy_082 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_082, fv_syn_c1c] using (nb067_compact_fv_empty_0087 f)

theorem nb067_compact_fv_empty_0088 : (nb067_alpha_dummy_079) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0234 : (nb067_alpha_dummy_079) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_079, fv_syn_c1c] using (nb067_compact_fv_empty_0088)

theorem nb067_compact_fv_empty_0089 (f : Var) : (nb067_alpha_dummy_080 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0235 (f : Var) : (nb067_alpha_dummy_080 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_080, fv_syn_c1c] using (nb067_compact_fv_empty_0089 f)

theorem nb067_compact_fv_empty_0090 : (nb067_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0236 : (nb067_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_000, fv_syn_c1c] using (nb067_compact_fv_empty_0090)

theorem nb067_compact_fv_empty_0091 (f : Var) : f ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0237 (f : Var) : f ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb067_compact_fv_empty_0091 f)

theorem nb067_compact_envfresh_0015 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)), ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)), ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)), ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)), ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)), ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_107) (nb067_alpha_dummy_110 f) (nb067_wpp_notmem_0206) (nb067_wpp_notmem_0207 f) (TEnvFresh.consFresh (nb067_alpha_dummy_106) (nb067_alpha_dummy_109 f) (nb067_wpp_notmem_0208) (nb067_wpp_notmem_0209 f) (TEnvFresh.consFresh (nb067_alpha_dummy_105) (nb067_alpha_dummy_108 f) (nb067_wpp_notmem_0210) (nb067_wpp_notmem_0211 f) (TEnvFresh.consFresh (nb067_alpha_dummy_103) (nb067_alpha_dummy_104 f) (nb067_wpp_notmem_0212) (nb067_wpp_notmem_0213 f) (TEnvFresh.consFresh (nb067_alpha_dummy_099) (nb067_alpha_dummy_101 f) (nb067_wpp_notmem_0214) (nb067_wpp_notmem_0215 f) (TEnvFresh.consFresh (nb067_alpha_dummy_100) (nb067_alpha_dummy_102 f) (nb067_wpp_notmem_0216) (nb067_wpp_notmem_0217 f) (TEnvFresh.consFresh (nb067_alpha_dummy_092) (nb067_alpha_dummy_094 f) (nb067_wpp_notmem_0218) (nb067_wpp_notmem_0219 f) (TEnvFresh.consFresh (nb067_alpha_dummy_091) (nb067_alpha_dummy_093 f) (nb067_wpp_notmem_0220) (nb067_wpp_notmem_0221 f) (TEnvFresh.consFresh (nb067_alpha_dummy_097) (nb067_alpha_dummy_098 f) (nb067_wpp_notmem_0222) (nb067_wpp_notmem_0223 f) (TEnvFresh.consFresh (nb067_alpha_dummy_095) (nb067_alpha_dummy_096 f) (nb067_wpp_notmem_0224) (nb067_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0226) (nb067_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0228) (nb067_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0230) (nb067_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0232) (nb067_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0234) (nb067_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0236) (nb067_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb067_wpp_refl_0015 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)), ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)), ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)), ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)), ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)), ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)), ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)), ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)), ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)), ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0015 x y f)

theorem nb067_wpp_notmem_0238 : (nb067_alpha_dummy_107) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_107, fv_syn_c0] using (nb067_compact_fv_empty_0060)

theorem nb067_wpp_notmem_0239 (f : Var) : (nb067_alpha_dummy_110 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_110, fv_syn_c0] using (nb067_compact_fv_empty_0061 f)

theorem nb067_wpp_notmem_0240 : (nb067_alpha_dummy_106) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_106, fv_syn_c0] using (nb067_compact_fv_empty_0062)

theorem nb067_wpp_notmem_0241 (f : Var) : (nb067_alpha_dummy_109 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_109, fv_syn_c0] using (nb067_compact_fv_empty_0063 f)

theorem nb067_wpp_notmem_0242 : (nb067_alpha_dummy_105) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_105, fv_syn_c0] using (nb067_compact_fv_empty_0064)

theorem nb067_wpp_notmem_0243 (f : Var) : (nb067_alpha_dummy_108 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_108, fv_syn_c0] using (nb067_compact_fv_empty_0065 f)

theorem nb067_wpp_notmem_0244 : (nb067_alpha_dummy_103) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_103, fv_syn_c0] using (nb067_compact_fv_empty_0066)

theorem nb067_wpp_notmem_0245 (f : Var) : (nb067_alpha_dummy_104 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_104, fv_syn_c0] using (nb067_compact_fv_empty_0067 f)

theorem nb067_wpp_notmem_0246 : (nb067_alpha_dummy_099) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_099, fv_syn_c0] using (nb067_compact_fv_empty_0068)

theorem nb067_wpp_notmem_0247 (f : Var) : (nb067_alpha_dummy_101 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_101, fv_syn_c0] using (nb067_compact_fv_empty_0069 f)

theorem nb067_wpp_notmem_0248 : (nb067_alpha_dummy_100) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_100, fv_syn_c0] using (nb067_compact_fv_empty_0070)

theorem nb067_wpp_notmem_0249 (f : Var) : (nb067_alpha_dummy_102 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_102, fv_syn_c0] using (nb067_compact_fv_empty_0071 f)

theorem nb067_wpp_notmem_0250 : (nb067_alpha_dummy_092) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_092, fv_syn_c0] using (nb067_compact_fv_empty_0072)

theorem nb067_wpp_notmem_0251 (f : Var) : (nb067_alpha_dummy_094 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_094, fv_syn_c0] using (nb067_compact_fv_empty_0073 f)

theorem nb067_wpp_notmem_0252 : (nb067_alpha_dummy_091) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_091, fv_syn_c0] using (nb067_compact_fv_empty_0074)

theorem nb067_wpp_notmem_0253 (f : Var) : (nb067_alpha_dummy_093 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_093, fv_syn_c0] using (nb067_compact_fv_empty_0075 f)

theorem nb067_wpp_notmem_0254 : (nb067_alpha_dummy_097) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_097, fv_syn_c0] using (nb067_compact_fv_empty_0076)

theorem nb067_wpp_notmem_0255 (f : Var) : (nb067_alpha_dummy_098 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_098, fv_syn_c0] using (nb067_compact_fv_empty_0077 f)

theorem nb067_wpp_notmem_0256 : (nb067_alpha_dummy_095) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_095, fv_syn_c0] using (nb067_compact_fv_empty_0078)

theorem nb067_wpp_notmem_0257 (f : Var) : (nb067_alpha_dummy_096 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_096, fv_syn_c0] using (nb067_compact_fv_empty_0079 f)

theorem nb067_wpp_notmem_0258 : (nb067_alpha_dummy_084) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_084, fv_syn_c0] using (nb067_compact_fv_empty_0080)

theorem nb067_wpp_notmem_0259 (f : Var) : (nb067_alpha_dummy_087 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_087, fv_syn_c0] using (nb067_compact_fv_empty_0081 f)

theorem nb067_wpp_notmem_0260 : (nb067_alpha_dummy_083) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_083, fv_syn_c0] using (nb067_compact_fv_empty_0082)

theorem nb067_wpp_notmem_0261 (f : Var) : (nb067_alpha_dummy_086 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_086, fv_syn_c0] using (nb067_compact_fv_empty_0083 f)

theorem nb067_wpp_notmem_0262 : (nb067_alpha_dummy_089) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_089, fv_syn_c0] using (nb067_compact_fv_empty_0084)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
