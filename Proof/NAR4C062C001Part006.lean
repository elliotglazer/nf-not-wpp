import NAR4C062C001Part005

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

noncomputable def nb062_split_alpha_0007 (x : Var) (y : Var) (r : Var) (a : Var) : TAlphaWff [((nb062_alpha_dummy_058), (nb062_alpha_dummy_061 x y)), ((nb062_alpha_dummy_057), (nb062_alpha_dummy_060 x y)), ((nb062_alpha_dummy_056), (nb062_alpha_dummy_059 x y)), ((nb062_alpha_dummy_054), (nb062_alpha_dummy_055 x y)), ((nb062_alpha_dummy_050), (nb062_alpha_dummy_052 x y)), ((nb062_alpha_dummy_051), (nb062_alpha_dummy_053 x y)), ((nb062_alpha_dummy_076), (nb062_alpha_dummy_077 x y)), ((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb062_alpha_dummy_057)) (Class.cv (nb062_alpha_dummy_058))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb062_alpha_dummy_056)) (syn_cun (Class.cv (nb062_alpha_dummy_057)) (Class.cv (nb062_alpha_dummy_058)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb062_alpha_dummy_060 x y)) (Class.cv (nb062_alpha_dummy_061 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb062_alpha_dummy_059 x y)) (syn_cun (Class.cv (nb062_alpha_dummy_060 x y)) (Class.cv (nb062_alpha_dummy_061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0057 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0055 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0059 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0057 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0055 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0059 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb062_alpha_dummy_058), (nb062_alpha_dummy_061 x y)), ((nb062_alpha_dummy_057), (nb062_alpha_dummy_060 x y)), ((nb062_alpha_dummy_056), (nb062_alpha_dummy_059 x y)), ((nb062_alpha_dummy_054), (nb062_alpha_dummy_055 x y)), ((nb062_alpha_dummy_050), (nb062_alpha_dummy_052 x y)), ((nb062_alpha_dummy_051), (nb062_alpha_dummy_053 x y)), ((nb062_alpha_dummy_076), (nb062_alpha_dummy_077 x y)), ((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (syn_c0) (nb062_wpp_refl_0011 x y r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0063 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0063 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0067 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0067 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb062_wpp_notmem_0184 : (nb062_alpha_dummy_076) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_076, fv_syn_cnnc] using (nb062_compact_fv_empty_0056)

theorem nb062_wpp_notmem_0185 (x : Var) (y : Var) : (nb062_alpha_dummy_077 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_077, fv_syn_cnnc] using (nb062_compact_fv_empty_0057 x y)

theorem nb062_wpp_notmem_0186 : (nb062_alpha_dummy_074) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_074, fv_syn_cnnc] using (nb062_compact_fv_empty_0058)

theorem nb062_wpp_notmem_0187 (x : Var) (y : Var) : (nb062_alpha_dummy_075 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_075, fv_syn_cnnc] using (nb062_compact_fv_empty_0059 x y)

theorem nb062_wpp_notmem_0188 : (nb062_alpha_dummy_072) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_072, fv_syn_cnnc] using (nb062_compact_fv_empty_0060)

theorem nb062_wpp_notmem_0189 (x : Var) (y : Var) : (nb062_alpha_dummy_073 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_073, fv_syn_cnnc] using (nb062_compact_fv_empty_0061 x y)

theorem nb062_compact_envfresh_0012 (x : Var) (y : Var) (r : Var) (a : Var) : TEnvFresh [((nb062_alpha_dummy_054), (nb062_alpha_dummy_055 x y)), ((nb062_alpha_dummy_050), (nb062_alpha_dummy_052 x y)), ((nb062_alpha_dummy_051), (nb062_alpha_dummy_053 x y)), ((nb062_alpha_dummy_076), (nb062_alpha_dummy_077 x y)), ((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb062_alpha_dummy_054) (nb062_alpha_dummy_055 x y) (nb062_wpp_notmem_0154) (nb062_wpp_notmem_0155 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_050) (nb062_alpha_dummy_052 x y) (nb062_wpp_notmem_0156) (nb062_wpp_notmem_0157 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_051) (nb062_alpha_dummy_053 x y) (nb062_wpp_notmem_0158) (nb062_wpp_notmem_0159 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_076) (nb062_alpha_dummy_077 x y) (nb062_wpp_notmem_0184) (nb062_wpp_notmem_0185 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_074) (nb062_alpha_dummy_075 x y) (nb062_wpp_notmem_0186) (nb062_wpp_notmem_0187 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_043) (nb062_alpha_dummy_045 x y) (nb062_wpp_notmem_0160) (nb062_wpp_notmem_0161 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_042) (nb062_alpha_dummy_044 x y) (nb062_wpp_notmem_0162) (nb062_wpp_notmem_0163 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_072) (nb062_alpha_dummy_073 x y) (nb062_wpp_notmem_0188) (nb062_wpp_notmem_0189 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_046) (nb062_alpha_dummy_047 x y) (nb062_wpp_notmem_0166) (nb062_wpp_notmem_0167 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_003) y (nb062_wpp_notmem_0168) (nb062_wpp_notmem_0169 y) (TEnvFresh.consFresh (nb062_alpha_dummy_002) x (nb062_wpp_notmem_0170) (nb062_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb062_alpha_dummy_000) a (nb062_wpp_notmem_0066) (nb062_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb062_alpha_dummy_001) r (nb062_wpp_notmem_0068) (nb062_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb062_alpha_dummy_004) (nb062_alpha_dummy_005 x y r a) (nb062_wpp_notmem_0070) (nb062_wpp_notmem_0071 x y r a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb062_wpp_refl_0012 (x : Var) (y : Var) (r : Var) (a : Var) : TReflOn [((nb062_alpha_dummy_054), (nb062_alpha_dummy_055 x y)), ((nb062_alpha_dummy_050), (nb062_alpha_dummy_052 x y)), ((nb062_alpha_dummy_051), (nb062_alpha_dummy_053 x y)), ((nb062_alpha_dummy_076), (nb062_alpha_dummy_077 x y)), ((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb062_compact_envfresh_0012 x y r a)

noncomputable def nb062_split_alpha_0008 (x : Var) (y : Var) (r : Var) (a : Var) : TAlphaWff [((nb062_alpha_dummy_051), (nb062_alpha_dummy_053 x y)), ((nb062_alpha_dummy_076), (nb062_alpha_dummy_077 x y)), ((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (Wff.all (nb062_alpha_dummy_050) (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb062_alpha_dummy_050)) (Class.cv (nb062_alpha_dummy_043))) (Wff.classEq (Class.cv (nb062_alpha_dummy_051)) (syn_cif (Wff.classMem (Class.cv (nb062_alpha_dummy_050)) (syn_cnnc)) (syn_cplc (Class.cv (nb062_alpha_dummy_050)) (syn_c1c)) (Class.cv (nb062_alpha_dummy_050))))))) (Wff.all (nb062_alpha_dummy_052 x y) (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb062_alpha_dummy_052 x y)) (Class.cv (nb062_alpha_dummy_045 x y))) (Wff.classEq (Class.cv (nb062_alpha_dummy_053 x y)) (syn_cif (Wff.classMem (Class.cv (nb062_alpha_dummy_052 x y)) (syn_cnnc)) (syn_cplc (Class.cv (nb062_alpha_dummy_052 x y)) (syn_c1c)) (Class.cv (nb062_alpha_dummy_052 x y))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0049 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0049 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0079 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0077 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_043))).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_045 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0053 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0053 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb062_alpha_dummy_058), (nb062_alpha_dummy_061 x y)), ((nb062_alpha_dummy_057), (nb062_alpha_dummy_060 x y)), ((nb062_alpha_dummy_056), (nb062_alpha_dummy_059 x y)), ((nb062_alpha_dummy_054), (nb062_alpha_dummy_055 x y)), ((nb062_alpha_dummy_050), (nb062_alpha_dummy_052 x y)), ((nb062_alpha_dummy_051), (nb062_alpha_dummy_053 x y)), ((nb062_alpha_dummy_076), (nb062_alpha_dummy_077 x y)), ((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (syn_c1c) (nb062_wpp_refl_0010 x y r a))) (TAlphaWff.neg (TAlphaWff.neg (nb062_split_alpha_0007 x y r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb062_alpha_dummy_054), (nb062_alpha_dummy_055 x y)), ((nb062_alpha_dummy_050), (nb062_alpha_dummy_052 x y)), ((nb062_alpha_dummy_051), (nb062_alpha_dummy_053 x y)), ((nb062_alpha_dummy_076), (nb062_alpha_dummy_077 x y)), ((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (syn_cnnc) (nb062_wpp_refl_0012 x y r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb062_alpha_dummy_054), (nb062_alpha_dummy_055 x y)), ((nb062_alpha_dummy_050), (nb062_alpha_dummy_052 x y)), ((nb062_alpha_dummy_051), (nb062_alpha_dummy_053 x y)), ((nb062_alpha_dummy_076), (nb062_alpha_dummy_077 x y)), ((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (syn_cnnc) (nb062_wpp_refl_0012 x y r a)))))))))))))))

theorem nb062_wpp_notmem_0190 : (nb062_alpha_dummy_074) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_074, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0058)

theorem nb062_wpp_notmem_0191 (x : Var) (y : Var) : (nb062_alpha_dummy_075 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_075, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0059 x y)

theorem nb062_wpp_notmem_0192 : (nb062_alpha_dummy_043) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_043, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0044)

theorem nb062_wpp_notmem_0193 (x : Var) (y : Var) : (nb062_alpha_dummy_045 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0045 x y)

theorem nb062_wpp_notmem_0194 : (nb062_alpha_dummy_042) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_042, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0046)

theorem nb062_wpp_notmem_0195 (x : Var) (y : Var) : (nb062_alpha_dummy_044 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0047 x y)

theorem nb062_wpp_notmem_0196 : (nb062_alpha_dummy_072) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_072, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0060)

theorem nb062_wpp_notmem_0197 (x : Var) (y : Var) : (nb062_alpha_dummy_073 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_073, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0061 x y)

theorem nb062_wpp_notmem_0198 : (nb062_alpha_dummy_046) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0050)

theorem nb062_wpp_notmem_0199 (x : Var) (y : Var) : (nb062_alpha_dummy_047 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_047, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0051 x y)

theorem nb062_wpp_notmem_0200 : (nb062_alpha_dummy_003) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0052)

theorem nb062_wpp_notmem_0201 (y : Var) : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0053 y)

theorem nb062_wpp_notmem_0202 : (nb062_alpha_dummy_002) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb062_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0054)

theorem nb062_wpp_notmem_0203 (x : Var) : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb062_compact_fv_empty_0055 x)

theorem nb062_compact_envfresh_0013 (x : Var) (y : Var) (r : Var) (a : Var) : TEnvFresh [((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb062_alpha_dummy_074) (nb062_alpha_dummy_075 x y) (nb062_wpp_notmem_0190) (nb062_wpp_notmem_0191 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_043) (nb062_alpha_dummy_045 x y) (nb062_wpp_notmem_0192) (nb062_wpp_notmem_0193 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_042) (nb062_alpha_dummy_044 x y) (nb062_wpp_notmem_0194) (nb062_wpp_notmem_0195 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_072) (nb062_alpha_dummy_073 x y) (nb062_wpp_notmem_0196) (nb062_wpp_notmem_0197 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_046) (nb062_alpha_dummy_047 x y) (nb062_wpp_notmem_0198) (nb062_wpp_notmem_0199 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_003) y (nb062_wpp_notmem_0200) (nb062_wpp_notmem_0201 y) (TEnvFresh.consFresh (nb062_alpha_dummy_002) x (nb062_wpp_notmem_0202) (nb062_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb062_alpha_dummy_000) a (nb062_wpp_notmem_0100) (nb062_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb062_alpha_dummy_001) r (nb062_wpp_notmem_0102) (nb062_wpp_notmem_0103 r) (TEnvFresh.consFresh (nb062_alpha_dummy_004) (nb062_alpha_dummy_005 x y r a) (nb062_wpp_notmem_0104) (nb062_wpp_notmem_0105 x y r a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))

noncomputable def nb062_wpp_refl_0013 (x : Var) (y : Var) (r : Var) (a : Var) : TReflOn [((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb062_compact_envfresh_0013 x y r a)

noncomputable def nb062_split_alpha_0009 (x : Var) (y : Var) (r : Var) (a : Var) (dv_x_y : x ≠ y) : TAlphaWff [((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (Wff.imp (Wff.classMem (Class.cv (nb062_alpha_dummy_046)) (syn_ccompl (Class.cab (nb062_alpha_dummy_042) (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_002)) (Wff.classEq (Class.cv (nb062_alpha_dummy_042)) (syn_cphi (Class.cv (nb062_alpha_dummy_043)))))))) (Wff.neg (Wff.classMem (Class.cv (nb062_alpha_dummy_046)) (syn_ccompl (Class.cab (nb062_alpha_dummy_042) (syn_wrex (nb062_alpha_dummy_043) (Class.cv (nb062_alpha_dummy_003)) (Wff.classEq (Class.cv (nb062_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_043))) (syn_csn (syn_c0c)))))))))) (Wff.imp (Wff.classMem (Class.cv (nb062_alpha_dummy_047 x y)) (syn_ccompl (Class.cab (nb062_alpha_dummy_044 x y) (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y)))))))) (Wff.neg (Wff.classMem (Class.cv (nb062_alpha_dummy_047 x y)) (syn_ccompl (Class.cab (nb062_alpha_dummy_044 x y) (syn_wrex (nb062_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb062_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb062_alpha_dummy_045 x y))) (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb062_split_alpha_0006 x y r a dv_x_y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb062_split_alpha_0006 x y r a dv_x_y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0075 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0071) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0073 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (nb062_split_alpha_0008 x y r a)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (nb062_split_alpha_0008 x y r a)))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb062_wpp_refl_0013 x y r a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0075 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0071) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0073 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_002))).fv ∪ ((Class.cv (nb062_alpha_dummy_003))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (nb062_split_alpha_0008 x y r a)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (nb062_split_alpha_0008 x y r a)))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb062_alpha_dummy_074), (nb062_alpha_dummy_075 x y)), ((nb062_alpha_dummy_043), (nb062_alpha_dummy_045 x y)), ((nb062_alpha_dummy_042), (nb062_alpha_dummy_044 x y)), ((nb062_alpha_dummy_072), (nb062_alpha_dummy_073 x y)), ((nb062_alpha_dummy_046), (nb062_alpha_dummy_047 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb062_wpp_refl_0013 x y r a)))))))))))))))))))))))))

theorem nb062_compact_fv_empty_0062 : (nb062_alpha_dummy_094) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0204 : (nb062_alpha_dummy_094) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_094, fv_syn_c1c] using (nb062_compact_fv_empty_0062)

theorem nb062_compact_fv_empty_0063 (x : Var) (y : Var) : (nb062_alpha_dummy_097 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0205 (x : Var) (y : Var) : (nb062_alpha_dummy_097 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_097, fv_syn_c1c] using (nb062_compact_fv_empty_0063 x y)

theorem nb062_compact_fv_empty_0064 : (nb062_alpha_dummy_093) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0206 : (nb062_alpha_dummy_093) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_093, fv_syn_c1c] using (nb062_compact_fv_empty_0064)

theorem nb062_compact_fv_empty_0065 (x : Var) (y : Var) : (nb062_alpha_dummy_096 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0207 (x : Var) (y : Var) : (nb062_alpha_dummy_096 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_096, fv_syn_c1c] using (nb062_compact_fv_empty_0065 x y)

theorem nb062_compact_fv_empty_0066 : (nb062_alpha_dummy_092) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0208 : (nb062_alpha_dummy_092) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_092, fv_syn_c1c] using (nb062_compact_fv_empty_0066)

theorem nb062_compact_fv_empty_0067 (x : Var) (y : Var) : (nb062_alpha_dummy_095 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0209 (x : Var) (y : Var) : (nb062_alpha_dummy_095 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_095, fv_syn_c1c] using (nb062_compact_fv_empty_0067 x y)

theorem nb062_compact_fv_empty_0068 : (nb062_alpha_dummy_090) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0210 : (nb062_alpha_dummy_090) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_090, fv_syn_c1c] using (nb062_compact_fv_empty_0068)

theorem nb062_compact_fv_empty_0069 (x : Var) (y : Var) : (nb062_alpha_dummy_091 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0211 (x : Var) (y : Var) : (nb062_alpha_dummy_091 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_091, fv_syn_c1c] using (nb062_compact_fv_empty_0069 x y)

theorem nb062_compact_fv_empty_0070 : (nb062_alpha_dummy_086) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0212 : (nb062_alpha_dummy_086) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_086, fv_syn_c1c] using (nb062_compact_fv_empty_0070)

theorem nb062_compact_fv_empty_0071 (x : Var) (y : Var) : (nb062_alpha_dummy_088 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0213 (x : Var) (y : Var) : (nb062_alpha_dummy_088 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_088, fv_syn_c1c] using (nb062_compact_fv_empty_0071 x y)

theorem nb062_compact_fv_empty_0072 : (nb062_alpha_dummy_087) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0214 : (nb062_alpha_dummy_087) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_087, fv_syn_c1c] using (nb062_compact_fv_empty_0072)

theorem nb062_compact_fv_empty_0073 (x : Var) (y : Var) : (nb062_alpha_dummy_089 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0215 (x : Var) (y : Var) : (nb062_alpha_dummy_089 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_089, fv_syn_c1c] using (nb062_compact_fv_empty_0073 x y)

theorem nb062_compact_fv_empty_0074 : (nb062_alpha_dummy_079) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0216 : (nb062_alpha_dummy_079) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_079, fv_syn_c1c] using (nb062_compact_fv_empty_0074)

theorem nb062_compact_fv_empty_0075 (x : Var) (y : Var) : (nb062_alpha_dummy_081 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0217 (x : Var) (y : Var) : (nb062_alpha_dummy_081 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_081, fv_syn_c1c] using (nb062_compact_fv_empty_0075 x y)

theorem nb062_compact_fv_empty_0076 : (nb062_alpha_dummy_078) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0218 : (nb062_alpha_dummy_078) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_078, fv_syn_c1c] using (nb062_compact_fv_empty_0076)

theorem nb062_compact_fv_empty_0077 (x : Var) (y : Var) : (nb062_alpha_dummy_080 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0219 (x : Var) (y : Var) : (nb062_alpha_dummy_080 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_080, fv_syn_c1c] using (nb062_compact_fv_empty_0077 x y)

theorem nb062_compact_fv_empty_0078 : (nb062_alpha_dummy_084) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0220 : (nb062_alpha_dummy_084) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_084, fv_syn_c1c] using (nb062_compact_fv_empty_0078)

theorem nb062_compact_fv_empty_0079 (x : Var) (y : Var) : (nb062_alpha_dummy_085 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0221 (x : Var) (y : Var) : (nb062_alpha_dummy_085 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_085, fv_syn_c1c] using (nb062_compact_fv_empty_0079 x y)

theorem nb062_compact_fv_empty_0080 : (nb062_alpha_dummy_082) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0222 : (nb062_alpha_dummy_082) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_082, fv_syn_c1c] using (nb062_compact_fv_empty_0080)

theorem nb062_compact_fv_empty_0081 (x : Var) (y : Var) : (nb062_alpha_dummy_083 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb062_wpp_notmem_0223 (x : Var) (y : Var) : (nb062_alpha_dummy_083 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb062_alpha_dummy_083, fv_syn_c1c] using (nb062_compact_fv_empty_0081 x y)

theorem nb062_compact_envfresh_0014 (x : Var) (y : Var) (r : Var) (a : Var) : TEnvFresh [((nb062_alpha_dummy_094), (nb062_alpha_dummy_097 x y)), ((nb062_alpha_dummy_093), (nb062_alpha_dummy_096 x y)), ((nb062_alpha_dummy_092), (nb062_alpha_dummy_095 x y)), ((nb062_alpha_dummy_090), (nb062_alpha_dummy_091 x y)), ((nb062_alpha_dummy_086), (nb062_alpha_dummy_088 x y)), ((nb062_alpha_dummy_087), (nb062_alpha_dummy_089 x y)), ((nb062_alpha_dummy_079), (nb062_alpha_dummy_081 x y)), ((nb062_alpha_dummy_078), (nb062_alpha_dummy_080 x y)), ((nb062_alpha_dummy_084), (nb062_alpha_dummy_085 x y)), ((nb062_alpha_dummy_082), (nb062_alpha_dummy_083 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb062_alpha_dummy_094) (nb062_alpha_dummy_097 x y) (nb062_wpp_notmem_0204) (nb062_wpp_notmem_0205 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_093) (nb062_alpha_dummy_096 x y) (nb062_wpp_notmem_0206) (nb062_wpp_notmem_0207 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_092) (nb062_alpha_dummy_095 x y) (nb062_wpp_notmem_0208) (nb062_wpp_notmem_0209 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_090) (nb062_alpha_dummy_091 x y) (nb062_wpp_notmem_0210) (nb062_wpp_notmem_0211 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_086) (nb062_alpha_dummy_088 x y) (nb062_wpp_notmem_0212) (nb062_wpp_notmem_0213 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_087) (nb062_alpha_dummy_089 x y) (nb062_wpp_notmem_0214) (nb062_wpp_notmem_0215 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_079) (nb062_alpha_dummy_081 x y) (nb062_wpp_notmem_0216) (nb062_wpp_notmem_0217 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_078) (nb062_alpha_dummy_080 x y) (nb062_wpp_notmem_0218) (nb062_wpp_notmem_0219 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_084) (nb062_alpha_dummy_085 x y) (nb062_wpp_notmem_0220) (nb062_wpp_notmem_0221 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_082) (nb062_alpha_dummy_083 x y) (nb062_wpp_notmem_0222) (nb062_wpp_notmem_0223 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_003) y (nb062_wpp_notmem_0126) (nb062_wpp_notmem_0127 y) (TEnvFresh.consFresh (nb062_alpha_dummy_002) x (nb062_wpp_notmem_0128) (nb062_wpp_notmem_0129 x) (TEnvFresh.consFresh (nb062_alpha_dummy_000) a (nb062_wpp_notmem_0020) (nb062_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb062_alpha_dummy_001) r (nb062_wpp_notmem_0022) (nb062_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb062_alpha_dummy_004) (nb062_alpha_dummy_005 x y r a) (nb062_wpp_notmem_0024) (nb062_wpp_notmem_0025 x y r a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb062_wpp_refl_0014 (x : Var) (y : Var) (r : Var) (a : Var) : TReflOn [((nb062_alpha_dummy_094), (nb062_alpha_dummy_097 x y)), ((nb062_alpha_dummy_093), (nb062_alpha_dummy_096 x y)), ((nb062_alpha_dummy_092), (nb062_alpha_dummy_095 x y)), ((nb062_alpha_dummy_090), (nb062_alpha_dummy_091 x y)), ((nb062_alpha_dummy_086), (nb062_alpha_dummy_088 x y)), ((nb062_alpha_dummy_087), (nb062_alpha_dummy_089 x y)), ((nb062_alpha_dummy_079), (nb062_alpha_dummy_081 x y)), ((nb062_alpha_dummy_078), (nb062_alpha_dummy_080 x y)), ((nb062_alpha_dummy_084), (nb062_alpha_dummy_085 x y)), ((nb062_alpha_dummy_082), (nb062_alpha_dummy_083 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb062_compact_envfresh_0014 x y r a)

theorem nb062_wpp_notmem_0224 : (nb062_alpha_dummy_094) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_094, fv_syn_c0] using (nb062_compact_fv_empty_0062)

theorem nb062_wpp_notmem_0225 (x : Var) (y : Var) : (nb062_alpha_dummy_097 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_097, fv_syn_c0] using (nb062_compact_fv_empty_0063 x y)

theorem nb062_wpp_notmem_0226 : (nb062_alpha_dummy_093) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_093, fv_syn_c0] using (nb062_compact_fv_empty_0064)

theorem nb062_wpp_notmem_0227 (x : Var) (y : Var) : (nb062_alpha_dummy_096 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_096, fv_syn_c0] using (nb062_compact_fv_empty_0065 x y)

theorem nb062_wpp_notmem_0228 : (nb062_alpha_dummy_092) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_092, fv_syn_c0] using (nb062_compact_fv_empty_0066)

theorem nb062_wpp_notmem_0229 (x : Var) (y : Var) : (nb062_alpha_dummy_095 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_095, fv_syn_c0] using (nb062_compact_fv_empty_0067 x y)

theorem nb062_wpp_notmem_0230 : (nb062_alpha_dummy_090) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_090, fv_syn_c0] using (nb062_compact_fv_empty_0068)

theorem nb062_wpp_notmem_0231 (x : Var) (y : Var) : (nb062_alpha_dummy_091 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_091, fv_syn_c0] using (nb062_compact_fv_empty_0069 x y)

theorem nb062_wpp_notmem_0232 : (nb062_alpha_dummy_086) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_086, fv_syn_c0] using (nb062_compact_fv_empty_0070)

theorem nb062_wpp_notmem_0233 (x : Var) (y : Var) : (nb062_alpha_dummy_088 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_088, fv_syn_c0] using (nb062_compact_fv_empty_0071 x y)

theorem nb062_wpp_notmem_0234 : (nb062_alpha_dummy_087) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_087, fv_syn_c0] using (nb062_compact_fv_empty_0072)

theorem nb062_wpp_notmem_0235 (x : Var) (y : Var) : (nb062_alpha_dummy_089 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_089, fv_syn_c0] using (nb062_compact_fv_empty_0073 x y)

theorem nb062_wpp_notmem_0236 : (nb062_alpha_dummy_079) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_079, fv_syn_c0] using (nb062_compact_fv_empty_0074)

theorem nb062_wpp_notmem_0237 (x : Var) (y : Var) : (nb062_alpha_dummy_081 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_081, fv_syn_c0] using (nb062_compact_fv_empty_0075 x y)

theorem nb062_wpp_notmem_0238 : (nb062_alpha_dummy_078) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_078, fv_syn_c0] using (nb062_compact_fv_empty_0076)

theorem nb062_wpp_notmem_0239 (x : Var) (y : Var) : (nb062_alpha_dummy_080 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_080, fv_syn_c0] using (nb062_compact_fv_empty_0077 x y)

theorem nb062_wpp_notmem_0240 : (nb062_alpha_dummy_084) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_084, fv_syn_c0] using (nb062_compact_fv_empty_0078)

theorem nb062_wpp_notmem_0241 (x : Var) (y : Var) : (nb062_alpha_dummy_085 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_085, fv_syn_c0] using (nb062_compact_fv_empty_0079 x y)

theorem nb062_wpp_notmem_0242 : (nb062_alpha_dummy_082) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_082, fv_syn_c0] using (nb062_compact_fv_empty_0080)

theorem nb062_wpp_notmem_0243 (x : Var) (y : Var) : (nb062_alpha_dummy_083 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb062_alpha_dummy_083, fv_syn_c0] using (nb062_compact_fv_empty_0081 x y)

theorem nb062_compact_envfresh_0015 (x : Var) (y : Var) (r : Var) (a : Var) : TEnvFresh [((nb062_alpha_dummy_094), (nb062_alpha_dummy_097 x y)), ((nb062_alpha_dummy_093), (nb062_alpha_dummy_096 x y)), ((nb062_alpha_dummy_092), (nb062_alpha_dummy_095 x y)), ((nb062_alpha_dummy_090), (nb062_alpha_dummy_091 x y)), ((nb062_alpha_dummy_086), (nb062_alpha_dummy_088 x y)), ((nb062_alpha_dummy_087), (nb062_alpha_dummy_089 x y)), ((nb062_alpha_dummy_079), (nb062_alpha_dummy_081 x y)), ((nb062_alpha_dummy_078), (nb062_alpha_dummy_080 x y)), ((nb062_alpha_dummy_084), (nb062_alpha_dummy_085 x y)), ((nb062_alpha_dummy_082), (nb062_alpha_dummy_083 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb062_alpha_dummy_094) (nb062_alpha_dummy_097 x y) (nb062_wpp_notmem_0224) (nb062_wpp_notmem_0225 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_093) (nb062_alpha_dummy_096 x y) (nb062_wpp_notmem_0226) (nb062_wpp_notmem_0227 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_092) (nb062_alpha_dummy_095 x y) (nb062_wpp_notmem_0228) (nb062_wpp_notmem_0229 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_090) (nb062_alpha_dummy_091 x y) (nb062_wpp_notmem_0230) (nb062_wpp_notmem_0231 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_086) (nb062_alpha_dummy_088 x y) (nb062_wpp_notmem_0232) (nb062_wpp_notmem_0233 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_087) (nb062_alpha_dummy_089 x y) (nb062_wpp_notmem_0234) (nb062_wpp_notmem_0235 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_079) (nb062_alpha_dummy_081 x y) (nb062_wpp_notmem_0236) (nb062_wpp_notmem_0237 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_078) (nb062_alpha_dummy_080 x y) (nb062_wpp_notmem_0238) (nb062_wpp_notmem_0239 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_084) (nb062_alpha_dummy_085 x y) (nb062_wpp_notmem_0240) (nb062_wpp_notmem_0241 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_082) (nb062_alpha_dummy_083 x y) (nb062_wpp_notmem_0242) (nb062_wpp_notmem_0243 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_003) y (nb062_wpp_notmem_0150) (nb062_wpp_notmem_0151 y) (TEnvFresh.consFresh (nb062_alpha_dummy_002) x (nb062_wpp_notmem_0152) (nb062_wpp_notmem_0153 x) (TEnvFresh.consFresh (nb062_alpha_dummy_000) a (nb062_wpp_notmem_0046) (nb062_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb062_alpha_dummy_001) r (nb062_wpp_notmem_0048) (nb062_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb062_alpha_dummy_004) (nb062_alpha_dummy_005 x y r a) (nb062_wpp_notmem_0050) (nb062_wpp_notmem_0051 x y r a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb062_wpp_refl_0015 (x : Var) (y : Var) (r : Var) (a : Var) : TReflOn [((nb062_alpha_dummy_094), (nb062_alpha_dummy_097 x y)), ((nb062_alpha_dummy_093), (nb062_alpha_dummy_096 x y)), ((nb062_alpha_dummy_092), (nb062_alpha_dummy_095 x y)), ((nb062_alpha_dummy_090), (nb062_alpha_dummy_091 x y)), ((nb062_alpha_dummy_086), (nb062_alpha_dummy_088 x y)), ((nb062_alpha_dummy_087), (nb062_alpha_dummy_089 x y)), ((nb062_alpha_dummy_079), (nb062_alpha_dummy_081 x y)), ((nb062_alpha_dummy_078), (nb062_alpha_dummy_080 x y)), ((nb062_alpha_dummy_084), (nb062_alpha_dummy_085 x y)), ((nb062_alpha_dummy_082), (nb062_alpha_dummy_083 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb062_compact_envfresh_0015 x y r a)

noncomputable def nb062_split_alpha_0010 (x : Var) (y : Var) (r : Var) (a : Var) : TAlphaWff [((nb062_alpha_dummy_094), (nb062_alpha_dummy_097 x y)), ((nb062_alpha_dummy_093), (nb062_alpha_dummy_096 x y)), ((nb062_alpha_dummy_092), (nb062_alpha_dummy_095 x y)), ((nb062_alpha_dummy_090), (nb062_alpha_dummy_091 x y)), ((nb062_alpha_dummy_086), (nb062_alpha_dummy_088 x y)), ((nb062_alpha_dummy_087), (nb062_alpha_dummy_089 x y)), ((nb062_alpha_dummy_079), (nb062_alpha_dummy_081 x y)), ((nb062_alpha_dummy_078), (nb062_alpha_dummy_080 x y)), ((nb062_alpha_dummy_084), (nb062_alpha_dummy_085 x y)), ((nb062_alpha_dummy_082), (nb062_alpha_dummy_083 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb062_alpha_dummy_093)) (Class.cv (nb062_alpha_dummy_094))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb062_alpha_dummy_092)) (syn_cun (Class.cv (nb062_alpha_dummy_093)) (Class.cv (nb062_alpha_dummy_094)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb062_alpha_dummy_096 x y)) (Class.cv (nb062_alpha_dummy_097 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb062_alpha_dummy_095 x y)) (syn_cun (Class.cv (nb062_alpha_dummy_096 x y)) (Class.cv (nb062_alpha_dummy_097 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0095 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0093 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0099 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0097 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0095 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0093 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0099 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0097 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb062_alpha_dummy_094), (nb062_alpha_dummy_097 x y)), ((nb062_alpha_dummy_093), (nb062_alpha_dummy_096 x y)), ((nb062_alpha_dummy_092), (nb062_alpha_dummy_095 x y)), ((nb062_alpha_dummy_090), (nb062_alpha_dummy_091 x y)), ((nb062_alpha_dummy_086), (nb062_alpha_dummy_088 x y)), ((nb062_alpha_dummy_087), (nb062_alpha_dummy_089 x y)), ((nb062_alpha_dummy_079), (nb062_alpha_dummy_081 x y)), ((nb062_alpha_dummy_078), (nb062_alpha_dummy_080 x y)), ((nb062_alpha_dummy_084), (nb062_alpha_dummy_085 x y)), ((nb062_alpha_dummy_082), (nb062_alpha_dummy_083 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] (syn_c0) (nb062_wpp_refl_0015 x y r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0103 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0101 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0103 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0101 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb062_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb062_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0107 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0105 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0107 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0105 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb062_wpp_notmem_0244 : (nb062_alpha_dummy_090) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_090, fv_syn_cnnc] using (nb062_compact_fv_empty_0068)

theorem nb062_wpp_notmem_0245 (x : Var) (y : Var) : (nb062_alpha_dummy_091 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_091, fv_syn_cnnc] using (nb062_compact_fv_empty_0069 x y)

theorem nb062_wpp_notmem_0246 : (nb062_alpha_dummy_086) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_086, fv_syn_cnnc] using (nb062_compact_fv_empty_0070)

theorem nb062_wpp_notmem_0247 (x : Var) (y : Var) : (nb062_alpha_dummy_088 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_088, fv_syn_cnnc] using (nb062_compact_fv_empty_0071 x y)

theorem nb062_wpp_notmem_0248 : (nb062_alpha_dummy_087) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_087, fv_syn_cnnc] using (nb062_compact_fv_empty_0072)

theorem nb062_wpp_notmem_0249 (x : Var) (y : Var) : (nb062_alpha_dummy_089 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_089, fv_syn_cnnc] using (nb062_compact_fv_empty_0073 x y)

theorem nb062_wpp_notmem_0250 : (nb062_alpha_dummy_079) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_079, fv_syn_cnnc] using (nb062_compact_fv_empty_0074)

theorem nb062_wpp_notmem_0251 (x : Var) (y : Var) : (nb062_alpha_dummy_081 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_081, fv_syn_cnnc] using (nb062_compact_fv_empty_0075 x y)

theorem nb062_wpp_notmem_0252 : (nb062_alpha_dummy_078) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_078, fv_syn_cnnc] using (nb062_compact_fv_empty_0076)

theorem nb062_wpp_notmem_0253 (x : Var) (y : Var) : (nb062_alpha_dummy_080 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_080, fv_syn_cnnc] using (nb062_compact_fv_empty_0077 x y)

theorem nb062_wpp_notmem_0254 : (nb062_alpha_dummy_084) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_084, fv_syn_cnnc] using (nb062_compact_fv_empty_0078)

theorem nb062_wpp_notmem_0255 (x : Var) (y : Var) : (nb062_alpha_dummy_085 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_085, fv_syn_cnnc] using (nb062_compact_fv_empty_0079 x y)

theorem nb062_wpp_notmem_0256 : (nb062_alpha_dummy_082) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_082, fv_syn_cnnc] using (nb062_compact_fv_empty_0080)

theorem nb062_wpp_notmem_0257 (x : Var) (y : Var) : (nb062_alpha_dummy_083 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb062_alpha_dummy_083, fv_syn_cnnc] using (nb062_compact_fv_empty_0081 x y)

theorem nb062_compact_envfresh_0016 (x : Var) (y : Var) (r : Var) (a : Var) : TEnvFresh [((nb062_alpha_dummy_090), (nb062_alpha_dummy_091 x y)), ((nb062_alpha_dummy_086), (nb062_alpha_dummy_088 x y)), ((nb062_alpha_dummy_087), (nb062_alpha_dummy_089 x y)), ((nb062_alpha_dummy_079), (nb062_alpha_dummy_081 x y)), ((nb062_alpha_dummy_078), (nb062_alpha_dummy_080 x y)), ((nb062_alpha_dummy_084), (nb062_alpha_dummy_085 x y)), ((nb062_alpha_dummy_082), (nb062_alpha_dummy_083 x y)), ((nb062_alpha_dummy_003), y), ((nb062_alpha_dummy_002), x), ((nb062_alpha_dummy_000), a), ((nb062_alpha_dummy_001), r), ((nb062_alpha_dummy_004), (nb062_alpha_dummy_005 x y r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb062_alpha_dummy_090) (nb062_alpha_dummy_091 x y) (nb062_wpp_notmem_0244) (nb062_wpp_notmem_0245 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_086) (nb062_alpha_dummy_088 x y) (nb062_wpp_notmem_0246) (nb062_wpp_notmem_0247 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_087) (nb062_alpha_dummy_089 x y) (nb062_wpp_notmem_0248) (nb062_wpp_notmem_0249 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_079) (nb062_alpha_dummy_081 x y) (nb062_wpp_notmem_0250) (nb062_wpp_notmem_0251 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_078) (nb062_alpha_dummy_080 x y) (nb062_wpp_notmem_0252) (nb062_wpp_notmem_0253 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_084) (nb062_alpha_dummy_085 x y) (nb062_wpp_notmem_0254) (nb062_wpp_notmem_0255 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_082) (nb062_alpha_dummy_083 x y) (nb062_wpp_notmem_0256) (nb062_wpp_notmem_0257 x y) (TEnvFresh.consFresh (nb062_alpha_dummy_003) y (nb062_wpp_notmem_0168) (nb062_wpp_notmem_0169 y) (TEnvFresh.consFresh (nb062_alpha_dummy_002) x (nb062_wpp_notmem_0170) (nb062_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb062_alpha_dummy_000) a (nb062_wpp_notmem_0066) (nb062_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb062_alpha_dummy_001) r (nb062_wpp_notmem_0068) (nb062_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb062_alpha_dummy_004) (nb062_alpha_dummy_005 x y r a) (nb062_wpp_notmem_0070) (nb062_wpp_notmem_0071 x y r a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
