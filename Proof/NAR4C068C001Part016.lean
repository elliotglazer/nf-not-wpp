import NAR4C068C001Part015

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

noncomputable def nb068_split_alpha_0007 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_067)) (syn_cun (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_070 f)) (syn_cun (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0059 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0063 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0059 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0063 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0011 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0067 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0067 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0073 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0071 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0073 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0071 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_0208 : (nb068_alpha_dummy_087) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_087, fv_syn_cnnc] using (nb068_compact_fv_empty_0064)

theorem nb068_wpp_notmem_0209 (f : Var) : (nb068_alpha_dummy_088 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_088, fv_syn_cnnc] using (nb068_compact_fv_empty_0065 f)

theorem nb068_wpp_notmem_0210 : (nb068_alpha_dummy_085) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_085, fv_syn_cnnc] using (nb068_compact_fv_empty_0066)

theorem nb068_wpp_notmem_0211 (f : Var) : (nb068_alpha_dummy_086 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_086, fv_syn_cnnc] using (nb068_compact_fv_empty_0067 f)

theorem nb068_wpp_notmem_0212 : (nb068_alpha_dummy_083) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_083, fv_syn_cnnc] using (nb068_compact_fv_empty_0068)

theorem nb068_wpp_notmem_0213 (f : Var) : (nb068_alpha_dummy_084 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_084, fv_syn_cnnc] using (nb068_compact_fv_empty_0069 f)

theorem nb068_compact_envfresh_0012 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_065) (nb068_alpha_dummy_066 f) (nb068_wpp_notmem_0170) (nb068_wpp_notmem_0171 f) (TEnvFresh.consFresh (nb068_alpha_dummy_061) (nb068_alpha_dummy_063 f) (nb068_wpp_notmem_0172) (nb068_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb068_alpha_dummy_062) (nb068_alpha_dummy_064 f) (nb068_wpp_notmem_0174) (nb068_wpp_notmem_0175 f) (TEnvFresh.consFresh (nb068_alpha_dummy_087) (nb068_alpha_dummy_088 f) (nb068_wpp_notmem_0208) (nb068_wpp_notmem_0209 f) (TEnvFresh.consFresh (nb068_alpha_dummy_085) (nb068_alpha_dummy_086 f) (nb068_wpp_notmem_0210) (nb068_wpp_notmem_0211 f) (TEnvFresh.consFresh (nb068_alpha_dummy_054) (nb068_alpha_dummy_056 f) (nb068_wpp_notmem_0176) (nb068_wpp_notmem_0177 f) (TEnvFresh.consFresh (nb068_alpha_dummy_053) (nb068_alpha_dummy_055 f) (nb068_wpp_notmem_0178) (nb068_wpp_notmem_0179 f) (TEnvFresh.consFresh (nb068_alpha_dummy_083) (nb068_alpha_dummy_084 f) (nb068_wpp_notmem_0212) (nb068_wpp_notmem_0213 f) (TEnvFresh.consFresh (nb068_alpha_dummy_057) (nb068_alpha_dummy_058 f) (nb068_wpp_notmem_0182) (nb068_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0184) (nb068_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0186) (nb068_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0188) (nb068_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0190) (nb068_wpp_notmem_0191 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0192) (nb068_wpp_notmem_0193 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))

noncomputable def nb068_wpp_refl_0012 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0012 x y f)

noncomputable def nb068_split_alpha_0008 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (Class.cv (nb068_alpha_dummy_054))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_062)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_061)))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (Class.cv (nb068_alpha_dummy_056 f))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_064 f)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_063 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0083 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0081 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_054))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_056 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0056) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0057 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)), ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)), ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)), ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0010 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0007 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0012 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)), ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)), ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)), ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)), ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0012 x y f))))))))))))

theorem nb068_wpp_notmem_0214 : (nb068_alpha_dummy_085) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_085, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0066)

theorem nb068_wpp_notmem_0215 (f : Var) : (nb068_alpha_dummy_086 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_086, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0067 f)

theorem nb068_wpp_notmem_0216 : (nb068_alpha_dummy_054) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_054, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0044)

theorem nb068_wpp_notmem_0217 (f : Var) : (nb068_alpha_dummy_056 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_056, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0045 f)

theorem nb068_wpp_notmem_0218 : (nb068_alpha_dummy_053) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_053, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0046)

theorem nb068_wpp_notmem_0219 (f : Var) : (nb068_alpha_dummy_055 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_055, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0047 f)

theorem nb068_wpp_notmem_0220 : (nb068_alpha_dummy_083) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_083, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0068)

theorem nb068_wpp_notmem_0221 (f : Var) : (nb068_alpha_dummy_084 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_084, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0069 f)

theorem nb068_wpp_notmem_0222 : (nb068_alpha_dummy_057) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_057, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0050)

theorem nb068_wpp_notmem_0223 (f : Var) : (nb068_alpha_dummy_058 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_058, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0051 f)

theorem nb068_wpp_notmem_0224 : (nb068_alpha_dummy_046) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0052)

theorem nb068_wpp_notmem_0225 (f : Var) : (nb068_alpha_dummy_049 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_049, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0053 f)

theorem nb068_wpp_notmem_0226 : (nb068_alpha_dummy_045) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0054)

theorem nb068_wpp_notmem_0227 (f : Var) : (nb068_alpha_dummy_048 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_048, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0055 f)

theorem nb068_wpp_notmem_0228 : (nb068_alpha_dummy_051) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_051, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0056)

theorem nb068_wpp_notmem_0229 (f : Var) : (nb068_alpha_dummy_052 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_052, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0057 f)

theorem nb068_wpp_notmem_0230 : (nb068_alpha_dummy_043) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_043, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0058)

theorem nb068_wpp_notmem_0231 (f : Var) : (nb068_alpha_dummy_044 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0059 f)

theorem nb068_wpp_notmem_0232 : (nb068_alpha_dummy_041) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_041, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0060)

theorem nb068_wpp_notmem_0233 (f : Var) : (nb068_alpha_dummy_042 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_042, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0061 f)

theorem nb068_wpp_notmem_0234 : (nb068_alpha_dummy_000) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0062)

theorem nb068_wpp_notmem_0235 (f : Var) : f ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0063 f)

theorem nb068_compact_envfresh_0013 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_085) (nb068_alpha_dummy_086 f) (nb068_wpp_notmem_0214) (nb068_wpp_notmem_0215 f) (TEnvFresh.consFresh (nb068_alpha_dummy_054) (nb068_alpha_dummy_056 f) (nb068_wpp_notmem_0216) (nb068_wpp_notmem_0217 f) (TEnvFresh.consFresh (nb068_alpha_dummy_053) (nb068_alpha_dummy_055 f) (nb068_wpp_notmem_0218) (nb068_wpp_notmem_0219 f) (TEnvFresh.consFresh (nb068_alpha_dummy_083) (nb068_alpha_dummy_084 f) (nb068_wpp_notmem_0220) (nb068_wpp_notmem_0221 f) (TEnvFresh.consFresh (nb068_alpha_dummy_057) (nb068_alpha_dummy_058 f) (nb068_wpp_notmem_0222) (nb068_wpp_notmem_0223 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0224) (nb068_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0226) (nb068_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0228) (nb068_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0230) (nb068_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0232) (nb068_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0234) (nb068_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0100) (nb068_wpp_notmem_0101 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0102) (nb068_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0104) (nb068_wpp_notmem_0105 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb068_wpp_refl_0013 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0013 x y f)

noncomputable def nb068_split_alpha_0009 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_083)) (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_083)) (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_084 f)) (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_084 f)) (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0079 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0075) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0077 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0008 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0008 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0013 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0079 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0075) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0077 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0008 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0008 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)), ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)), ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)), ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)), ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0013 x y f)))))))))))))))))))

theorem nb068_compact_fv_empty_0070 : (nb068_alpha_dummy_105) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0236 : (nb068_alpha_dummy_105) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_105, fv_syn_c1c] using (nb068_compact_fv_empty_0070)

theorem nb068_compact_fv_empty_0071 (f : Var) : (nb068_alpha_dummy_108 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0237 (f : Var) : (nb068_alpha_dummy_108 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_108, fv_syn_c1c] using (nb068_compact_fv_empty_0071 f)

theorem nb068_compact_fv_empty_0072 : (nb068_alpha_dummy_104) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0238 : (nb068_alpha_dummy_104) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_104, fv_syn_c1c] using (nb068_compact_fv_empty_0072)

theorem nb068_compact_fv_empty_0073 (f : Var) : (nb068_alpha_dummy_107 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0239 (f : Var) : (nb068_alpha_dummy_107 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_107, fv_syn_c1c] using (nb068_compact_fv_empty_0073 f)

theorem nb068_compact_fv_empty_0074 : (nb068_alpha_dummy_103) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0240 : (nb068_alpha_dummy_103) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_103, fv_syn_c1c] using (nb068_compact_fv_empty_0074)

theorem nb068_compact_fv_empty_0075 (f : Var) : (nb068_alpha_dummy_106 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0241 (f : Var) : (nb068_alpha_dummy_106 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_106, fv_syn_c1c] using (nb068_compact_fv_empty_0075 f)

theorem nb068_compact_fv_empty_0076 : (nb068_alpha_dummy_101) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0242 : (nb068_alpha_dummy_101) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_101, fv_syn_c1c] using (nb068_compact_fv_empty_0076)

theorem nb068_compact_fv_empty_0077 (f : Var) : (nb068_alpha_dummy_102 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0243 (f : Var) : (nb068_alpha_dummy_102 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_102, fv_syn_c1c] using (nb068_compact_fv_empty_0077 f)

theorem nb068_compact_fv_empty_0078 : (nb068_alpha_dummy_097) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0244 : (nb068_alpha_dummy_097) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_097, fv_syn_c1c] using (nb068_compact_fv_empty_0078)

theorem nb068_compact_fv_empty_0079 (f : Var) : (nb068_alpha_dummy_099 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0245 (f : Var) : (nb068_alpha_dummy_099 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_099, fv_syn_c1c] using (nb068_compact_fv_empty_0079 f)

theorem nb068_compact_fv_empty_0080 : (nb068_alpha_dummy_098) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0246 : (nb068_alpha_dummy_098) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_098, fv_syn_c1c] using (nb068_compact_fv_empty_0080)

theorem nb068_compact_fv_empty_0081 (f : Var) : (nb068_alpha_dummy_100 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0247 (f : Var) : (nb068_alpha_dummy_100 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_100, fv_syn_c1c] using (nb068_compact_fv_empty_0081 f)

theorem nb068_compact_fv_empty_0082 : (nb068_alpha_dummy_090) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0248 : (nb068_alpha_dummy_090) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_090, fv_syn_c1c] using (nb068_compact_fv_empty_0082)

theorem nb068_compact_fv_empty_0083 (f : Var) : (nb068_alpha_dummy_092 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0249 (f : Var) : (nb068_alpha_dummy_092 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_092, fv_syn_c1c] using (nb068_compact_fv_empty_0083 f)

theorem nb068_compact_fv_empty_0084 : (nb068_alpha_dummy_089) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0250 : (nb068_alpha_dummy_089) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_089, fv_syn_c1c] using (nb068_compact_fv_empty_0084)

theorem nb068_compact_fv_empty_0085 (f : Var) : (nb068_alpha_dummy_091 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0251 (f : Var) : (nb068_alpha_dummy_091 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_091, fv_syn_c1c] using (nb068_compact_fv_empty_0085 f)

theorem nb068_compact_fv_empty_0086 : (nb068_alpha_dummy_095) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0252 : (nb068_alpha_dummy_095) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_095, fv_syn_c1c] using (nb068_compact_fv_empty_0086)

theorem nb068_compact_fv_empty_0087 (f : Var) : (nb068_alpha_dummy_096 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0253 (f : Var) : (nb068_alpha_dummy_096 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_096, fv_syn_c1c] using (nb068_compact_fv_empty_0087 f)

theorem nb068_compact_fv_empty_0088 : (nb068_alpha_dummy_093) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0254 : (nb068_alpha_dummy_093) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_093, fv_syn_c1c] using (nb068_compact_fv_empty_0088)

theorem nb068_compact_fv_empty_0089 (f : Var) : (nb068_alpha_dummy_094 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0255 (f : Var) : (nb068_alpha_dummy_094 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_094, fv_syn_c1c] using (nb068_compact_fv_empty_0089 f)

theorem nb068_compact_fv_empty_0090 : (nb068_alpha_dummy_047) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0256 : (nb068_alpha_dummy_047) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_047, fv_syn_c1c] using (nb068_compact_fv_empty_0090)

theorem nb068_compact_fv_empty_0091 (f : Var) : (nb068_alpha_dummy_050 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0257 (f : Var) : (nb068_alpha_dummy_050 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_050, fv_syn_c1c] using (nb068_compact_fv_empty_0091 f)

theorem nb068_compact_envfresh_0014 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)), ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)), ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)), ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)), ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)), ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)), ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)), ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)), ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)), ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_105) (nb068_alpha_dummy_108 f) (nb068_wpp_notmem_0236) (nb068_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb068_alpha_dummy_104) (nb068_alpha_dummy_107 f) (nb068_wpp_notmem_0238) (nb068_wpp_notmem_0239 f) (TEnvFresh.consFresh (nb068_alpha_dummy_103) (nb068_alpha_dummy_106 f) (nb068_wpp_notmem_0240) (nb068_wpp_notmem_0241 f) (TEnvFresh.consFresh (nb068_alpha_dummy_101) (nb068_alpha_dummy_102 f) (nb068_wpp_notmem_0242) (nb068_wpp_notmem_0243 f) (TEnvFresh.consFresh (nb068_alpha_dummy_097) (nb068_alpha_dummy_099 f) (nb068_wpp_notmem_0244) (nb068_wpp_notmem_0245 f) (TEnvFresh.consFresh (nb068_alpha_dummy_098) (nb068_alpha_dummy_100 f) (nb068_wpp_notmem_0246) (nb068_wpp_notmem_0247 f) (TEnvFresh.consFresh (nb068_alpha_dummy_090) (nb068_alpha_dummy_092 f) (nb068_wpp_notmem_0248) (nb068_wpp_notmem_0249 f) (TEnvFresh.consFresh (nb068_alpha_dummy_089) (nb068_alpha_dummy_091 f) (nb068_wpp_notmem_0250) (nb068_wpp_notmem_0251 f) (TEnvFresh.consFresh (nb068_alpha_dummy_095) (nb068_alpha_dummy_096 f) (nb068_wpp_notmem_0252) (nb068_wpp_notmem_0253 f) (TEnvFresh.consFresh (nb068_alpha_dummy_093) (nb068_alpha_dummy_094 f) (nb068_wpp_notmem_0254) (nb068_wpp_notmem_0255 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0256) (nb068_wpp_notmem_0257 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0126) (nb068_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0128) (nb068_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0130) (nb068_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0132) (nb068_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0134) (nb068_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb068_wpp_refl_0014 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)), ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)), ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)), ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)), ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)), ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)), ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)), ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)), ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)), ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0014 x y f)

theorem nb068_wpp_notmem_0258 : (nb068_alpha_dummy_105) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_105, fv_syn_c0] using (nb068_compact_fv_empty_0070)

theorem nb068_wpp_notmem_0259 (f : Var) : (nb068_alpha_dummy_108 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_108, fv_syn_c0] using (nb068_compact_fv_empty_0071 f)

theorem nb068_wpp_notmem_0260 : (nb068_alpha_dummy_104) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_104, fv_syn_c0] using (nb068_compact_fv_empty_0072)

theorem nb068_wpp_notmem_0261 (f : Var) : (nb068_alpha_dummy_107 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_107, fv_syn_c0] using (nb068_compact_fv_empty_0073 f)

theorem nb068_wpp_notmem_0262 : (nb068_alpha_dummy_103) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_103, fv_syn_c0] using (nb068_compact_fv_empty_0074)

theorem nb068_wpp_notmem_0263 (f : Var) : (nb068_alpha_dummy_106 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_106, fv_syn_c0] using (nb068_compact_fv_empty_0075 f)

theorem nb068_wpp_notmem_0264 : (nb068_alpha_dummy_101) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_101, fv_syn_c0] using (nb068_compact_fv_empty_0076)

theorem nb068_wpp_notmem_0265 (f : Var) : (nb068_alpha_dummy_102 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_102, fv_syn_c0] using (nb068_compact_fv_empty_0077 f)

theorem nb068_wpp_notmem_0266 : (nb068_alpha_dummy_097) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_097, fv_syn_c0] using (nb068_compact_fv_empty_0078)

theorem nb068_wpp_notmem_0267 (f : Var) : (nb068_alpha_dummy_099 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_099, fv_syn_c0] using (nb068_compact_fv_empty_0079 f)

theorem nb068_wpp_notmem_0268 : (nb068_alpha_dummy_098) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_098, fv_syn_c0] using (nb068_compact_fv_empty_0080)

theorem nb068_wpp_notmem_0269 (f : Var) : (nb068_alpha_dummy_100 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_100, fv_syn_c0] using (nb068_compact_fv_empty_0081 f)

theorem nb068_wpp_notmem_0270 : (nb068_alpha_dummy_090) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_090, fv_syn_c0] using (nb068_compact_fv_empty_0082)

theorem nb068_wpp_notmem_0271 (f : Var) : (nb068_alpha_dummy_092 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_092, fv_syn_c0] using (nb068_compact_fv_empty_0083 f)

theorem nb068_wpp_notmem_0272 : (nb068_alpha_dummy_089) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_089, fv_syn_c0] using (nb068_compact_fv_empty_0084)

theorem nb068_wpp_notmem_0273 (f : Var) : (nb068_alpha_dummy_091 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_091, fv_syn_c0] using (nb068_compact_fv_empty_0085 f)

theorem nb068_wpp_notmem_0274 : (nb068_alpha_dummy_095) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_095, fv_syn_c0] using (nb068_compact_fv_empty_0086)

theorem nb068_wpp_notmem_0275 (f : Var) : (nb068_alpha_dummy_096 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_096, fv_syn_c0] using (nb068_compact_fv_empty_0087 f)

theorem nb068_wpp_notmem_0276 : (nb068_alpha_dummy_093) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_093, fv_syn_c0] using (nb068_compact_fv_empty_0088)

theorem nb068_wpp_notmem_0277 (f : Var) : (nb068_alpha_dummy_094 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_094, fv_syn_c0] using (nb068_compact_fv_empty_0089 f)

theorem nb068_wpp_notmem_0278 : (nb068_alpha_dummy_047) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_047, fv_syn_c0] using (nb068_compact_fv_empty_0090)

theorem nb068_wpp_notmem_0279 (f : Var) : (nb068_alpha_dummy_050 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_050, fv_syn_c0] using (nb068_compact_fv_empty_0091 f)

theorem nb068_compact_envfresh_0015 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)), ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)), ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)), ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)), ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)), ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)), ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)), ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)), ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)), ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_105) (nb068_alpha_dummy_108 f) (nb068_wpp_notmem_0258) (nb068_wpp_notmem_0259 f) (TEnvFresh.consFresh (nb068_alpha_dummy_104) (nb068_alpha_dummy_107 f) (nb068_wpp_notmem_0260) (nb068_wpp_notmem_0261 f) (TEnvFresh.consFresh (nb068_alpha_dummy_103) (nb068_alpha_dummy_106 f) (nb068_wpp_notmem_0262) (nb068_wpp_notmem_0263 f) (TEnvFresh.consFresh (nb068_alpha_dummy_101) (nb068_alpha_dummy_102 f) (nb068_wpp_notmem_0264) (nb068_wpp_notmem_0265 f) (TEnvFresh.consFresh (nb068_alpha_dummy_097) (nb068_alpha_dummy_099 f) (nb068_wpp_notmem_0266) (nb068_wpp_notmem_0267 f) (TEnvFresh.consFresh (nb068_alpha_dummy_098) (nb068_alpha_dummy_100 f) (nb068_wpp_notmem_0268) (nb068_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb068_alpha_dummy_090) (nb068_alpha_dummy_092 f) (nb068_wpp_notmem_0270) (nb068_wpp_notmem_0271 f) (TEnvFresh.consFresh (nb068_alpha_dummy_089) (nb068_alpha_dummy_091 f) (nb068_wpp_notmem_0272) (nb068_wpp_notmem_0273 f) (TEnvFresh.consFresh (nb068_alpha_dummy_095) (nb068_alpha_dummy_096 f) (nb068_wpp_notmem_0274) (nb068_wpp_notmem_0275 f) (TEnvFresh.consFresh (nb068_alpha_dummy_093) (nb068_alpha_dummy_094 f) (nb068_wpp_notmem_0276) (nb068_wpp_notmem_0277 f) (TEnvFresh.consFresh (nb068_alpha_dummy_047) (nb068_alpha_dummy_050 f) (nb068_wpp_notmem_0278) (nb068_wpp_notmem_0279 f) (TEnvFresh.consFresh (nb068_alpha_dummy_046) (nb068_alpha_dummy_049 f) (nb068_wpp_notmem_0158) (nb068_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb068_alpha_dummy_045) (nb068_alpha_dummy_048 f) (nb068_wpp_notmem_0160) (nb068_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb068_alpha_dummy_051) (nb068_alpha_dummy_052 f) (nb068_wpp_notmem_0162) (nb068_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f) (nb068_wpp_notmem_0164) (nb068_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f) (nb068_wpp_notmem_0166) (nb068_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb068_wpp_refl_0015 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)), ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)), ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)), ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)), ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)), ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)), ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)), ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)), ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)), ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)), ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)), ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)), ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)), ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)), ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)), ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0015 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
