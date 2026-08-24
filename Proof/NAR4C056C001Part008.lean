import NAR4C056C001Part007

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

theorem nb056_wpp_notmem_0192 : (nb056_alpha_dummy_081) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_081, fv_syn_c1c] using (nb056_compact_fv_empty_0062)

theorem nb056_compact_fv_empty_0063 (f : Var) : (nb056_alpha_dummy_082 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0193 (f : Var) : (nb056_alpha_dummy_082 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_082, fv_syn_c1c] using (nb056_compact_fv_empty_0063 f)

theorem nb056_compact_fv_empty_0064 : (nb056_alpha_dummy_079) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0194 : (nb056_alpha_dummy_079) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_079, fv_syn_c1c] using (nb056_compact_fv_empty_0064)

theorem nb056_compact_fv_empty_0065 (f : Var) : (nb056_alpha_dummy_080 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0195 (f : Var) : (nb056_alpha_dummy_080 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_080, fv_syn_c1c] using (nb056_compact_fv_empty_0065 f)

theorem nb056_compact_envfresh_0010 (f : Var) : TEnvFresh [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_065) (nb056_alpha_dummy_068 f) (nb056_wpp_notmem_0130) (nb056_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb056_alpha_dummy_064) (nb056_alpha_dummy_067 f) (nb056_wpp_notmem_0132) (nb056_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb056_alpha_dummy_063) (nb056_alpha_dummy_066 f) (nb056_wpp_notmem_0134) (nb056_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb056_alpha_dummy_061) (nb056_alpha_dummy_062 f) (nb056_wpp_notmem_0136) (nb056_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb056_alpha_dummy_057) (nb056_alpha_dummy_059 f) (nb056_wpp_notmem_0138) (nb056_wpp_notmem_0139 f) (TEnvFresh.consFresh (nb056_alpha_dummy_058) (nb056_alpha_dummy_060 f) (nb056_wpp_notmem_0140) (nb056_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb056_alpha_dummy_083) (nb056_alpha_dummy_084 f) (nb056_wpp_notmem_0190) (nb056_wpp_notmem_0191 f) (TEnvFresh.consFresh (nb056_alpha_dummy_081) (nb056_alpha_dummy_082 f) (nb056_wpp_notmem_0192) (nb056_wpp_notmem_0193 f) (TEnvFresh.consFresh (nb056_alpha_dummy_050) (nb056_alpha_dummy_052 f) (nb056_wpp_notmem_0142) (nb056_wpp_notmem_0143 f) (TEnvFresh.consFresh (nb056_alpha_dummy_049) (nb056_alpha_dummy_051 f) (nb056_wpp_notmem_0144) (nb056_wpp_notmem_0145 f) (TEnvFresh.consFresh (nb056_alpha_dummy_079) (nb056_alpha_dummy_080 f) (nb056_wpp_notmem_0194) (nb056_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb056_alpha_dummy_053) (nb056_alpha_dummy_054 f) (nb056_wpp_notmem_0148) (nb056_wpp_notmem_0149 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0150) (nb056_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0020) (nb056_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0022) (nb056_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0024) (nb056_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0026) (nb056_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0028) (nb056_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0030) (nb056_wpp_notmem_0031 f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb056_wpp_refl_0010 (f : Var) : TReflOn [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0010 f)

theorem nb056_wpp_notmem_0196 : (nb056_alpha_dummy_083) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_083, fv_syn_c0] using (nb056_compact_fv_empty_0060)

theorem nb056_wpp_notmem_0197 (f : Var) : (nb056_alpha_dummy_084 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_084, fv_syn_c0] using (nb056_compact_fv_empty_0061 f)

theorem nb056_wpp_notmem_0198 : (nb056_alpha_dummy_081) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_081, fv_syn_c0] using (nb056_compact_fv_empty_0062)

theorem nb056_wpp_notmem_0199 (f : Var) : (nb056_alpha_dummy_082 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_082, fv_syn_c0] using (nb056_compact_fv_empty_0063 f)

theorem nb056_wpp_notmem_0200 : (nb056_alpha_dummy_079) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_079, fv_syn_c0] using (nb056_compact_fv_empty_0064)

theorem nb056_wpp_notmem_0201 (f : Var) : (nb056_alpha_dummy_080 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_080, fv_syn_c0] using (nb056_compact_fv_empty_0065 f)

theorem nb056_compact_envfresh_0011 (f : Var) : TEnvFresh [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_065) (nb056_alpha_dummy_068 f) (nb056_wpp_notmem_0152) (nb056_wpp_notmem_0153 f) (TEnvFresh.consFresh (nb056_alpha_dummy_064) (nb056_alpha_dummy_067 f) (nb056_wpp_notmem_0154) (nb056_wpp_notmem_0155 f) (TEnvFresh.consFresh (nb056_alpha_dummy_063) (nb056_alpha_dummy_066 f) (nb056_wpp_notmem_0156) (nb056_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb056_alpha_dummy_061) (nb056_alpha_dummy_062 f) (nb056_wpp_notmem_0158) (nb056_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb056_alpha_dummy_057) (nb056_alpha_dummy_059 f) (nb056_wpp_notmem_0160) (nb056_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb056_alpha_dummy_058) (nb056_alpha_dummy_060 f) (nb056_wpp_notmem_0162) (nb056_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb056_alpha_dummy_083) (nb056_alpha_dummy_084 f) (nb056_wpp_notmem_0196) (nb056_wpp_notmem_0197 f) (TEnvFresh.consFresh (nb056_alpha_dummy_081) (nb056_alpha_dummy_082 f) (nb056_wpp_notmem_0198) (nb056_wpp_notmem_0199 f) (TEnvFresh.consFresh (nb056_alpha_dummy_050) (nb056_alpha_dummy_052 f) (nb056_wpp_notmem_0164) (nb056_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb056_alpha_dummy_049) (nb056_alpha_dummy_051 f) (nb056_wpp_notmem_0166) (nb056_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb056_alpha_dummy_079) (nb056_alpha_dummy_080 f) (nb056_wpp_notmem_0200) (nb056_wpp_notmem_0201 f) (TEnvFresh.consFresh (nb056_alpha_dummy_053) (nb056_alpha_dummy_054 f) (nb056_wpp_notmem_0170) (nb056_wpp_notmem_0171 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0172) (nb056_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0052) (nb056_wpp_notmem_0053 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0054) (nb056_wpp_notmem_0055 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0056) (nb056_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0058) (nb056_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0060) (nb056_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0062) (nb056_wpp_notmem_0063 f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb056_wpp_refl_0011 (f : Var) : TReflOn [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0011 f)

noncomputable def nb056_split_alpha_0007 (f : Var) : TAlphaWff [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_063)) (syn_cun (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_066 f)) (syn_cun (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c0) (nb056_wpp_refl_0011 f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb056_wpp_notmem_0202 : (nb056_alpha_dummy_083) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_083, fv_syn_cnnc] using (nb056_compact_fv_empty_0060)

theorem nb056_wpp_notmem_0203 (f : Var) : (nb056_alpha_dummy_084 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_084, fv_syn_cnnc] using (nb056_compact_fv_empty_0061 f)

theorem nb056_wpp_notmem_0204 : (nb056_alpha_dummy_081) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_081, fv_syn_cnnc] using (nb056_compact_fv_empty_0062)

theorem nb056_wpp_notmem_0205 (f : Var) : (nb056_alpha_dummy_082 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_082, fv_syn_cnnc] using (nb056_compact_fv_empty_0063 f)

theorem nb056_wpp_notmem_0206 : (nb056_alpha_dummy_079) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_079, fv_syn_cnnc] using (nb056_compact_fv_empty_0064)

theorem nb056_wpp_notmem_0207 (f : Var) : (nb056_alpha_dummy_080 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_080, fv_syn_cnnc] using (nb056_compact_fv_empty_0065 f)

theorem nb056_compact_envfresh_0012 (f : Var) : TEnvFresh [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_061) (nb056_alpha_dummy_062 f) (nb056_wpp_notmem_0174) (nb056_wpp_notmem_0175 f) (TEnvFresh.consFresh (nb056_alpha_dummy_057) (nb056_alpha_dummy_059 f) (nb056_wpp_notmem_0176) (nb056_wpp_notmem_0177 f) (TEnvFresh.consFresh (nb056_alpha_dummy_058) (nb056_alpha_dummy_060 f) (nb056_wpp_notmem_0178) (nb056_wpp_notmem_0179 f) (TEnvFresh.consFresh (nb056_alpha_dummy_083) (nb056_alpha_dummy_084 f) (nb056_wpp_notmem_0202) (nb056_wpp_notmem_0203 f) (TEnvFresh.consFresh (nb056_alpha_dummy_081) (nb056_alpha_dummy_082 f) (nb056_wpp_notmem_0204) (nb056_wpp_notmem_0205 f) (TEnvFresh.consFresh (nb056_alpha_dummy_050) (nb056_alpha_dummy_052 f) (nb056_wpp_notmem_0180) (nb056_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb056_alpha_dummy_049) (nb056_alpha_dummy_051 f) (nb056_wpp_notmem_0182) (nb056_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb056_alpha_dummy_079) (nb056_alpha_dummy_080 f) (nb056_wpp_notmem_0206) (nb056_wpp_notmem_0207 f) (TEnvFresh.consFresh (nb056_alpha_dummy_053) (nb056_alpha_dummy_054 f) (nb056_wpp_notmem_0186) (nb056_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0188) (nb056_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0078) (nb056_wpp_notmem_0079 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0080) (nb056_wpp_notmem_0081 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0082) (nb056_wpp_notmem_0083 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0084) (nb056_wpp_notmem_0085 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0086) (nb056_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0088) (nb056_wpp_notmem_0089 f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb056_wpp_refl_0012 (f : Var) : TReflOn [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0012 f)

noncomputable def nb056_split_alpha_0008 (f : Var) : TAlphaWff [((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (Class.cv (nb056_alpha_dummy_050))) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_058)) (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (syn_cnnc)) (syn_cplc (Class.cv (nb056_alpha_dummy_057)) (syn_c1c)) (Class.cv (nb056_alpha_dummy_057)))))) (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (Class.cv (nb056_alpha_dummy_052 f))) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_060 f)) (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb056_alpha_dummy_059 f)) (syn_c1c)) (Class.cv (nb056_alpha_dummy_059 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0079 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0077 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_050))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_052 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0053 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0053 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c1c) (nb056_wpp_refl_0010 f))) (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0007 f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0012 f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)), ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0012 f))))))))))))

theorem nb056_wpp_notmem_0208 : (nb056_alpha_dummy_081) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_081, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0062)

theorem nb056_wpp_notmem_0209 (f : Var) : (nb056_alpha_dummy_082 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_082, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0063 f)

theorem nb056_wpp_notmem_0210 : (nb056_alpha_dummy_050) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_050, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0050)

theorem nb056_wpp_notmem_0211 (f : Var) : (nb056_alpha_dummy_052 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_052, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0051 f)

theorem nb056_wpp_notmem_0212 : (nb056_alpha_dummy_049) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_049, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0052)

theorem nb056_wpp_notmem_0213 (f : Var) : (nb056_alpha_dummy_051 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_051, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0053 f)

theorem nb056_wpp_notmem_0214 : (nb056_alpha_dummy_079) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_079, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0064)

theorem nb056_wpp_notmem_0215 (f : Var) : (nb056_alpha_dummy_080 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_080, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0065 f)

theorem nb056_wpp_notmem_0216 : (nb056_alpha_dummy_053) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_053, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0056)

theorem nb056_wpp_notmem_0217 (f : Var) : (nb056_alpha_dummy_054 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_054, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0057 f)

theorem nb056_wpp_notmem_0218 : (nb056_alpha_dummy_007) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0058)

theorem nb056_wpp_notmem_0219 (f : Var) : (nb056_alpha_dummy_010 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0059 f)

theorem nb056_compact_envfresh_0013 (f : Var) : TEnvFresh [((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_081) (nb056_alpha_dummy_082 f) (nb056_wpp_notmem_0208) (nb056_wpp_notmem_0209 f) (TEnvFresh.consFresh (nb056_alpha_dummy_050) (nb056_alpha_dummy_052 f) (nb056_wpp_notmem_0210) (nb056_wpp_notmem_0211 f) (TEnvFresh.consFresh (nb056_alpha_dummy_049) (nb056_alpha_dummy_051 f) (nb056_wpp_notmem_0212) (nb056_wpp_notmem_0213 f) (TEnvFresh.consFresh (nb056_alpha_dummy_079) (nb056_alpha_dummy_080 f) (nb056_wpp_notmem_0214) (nb056_wpp_notmem_0215 f) (TEnvFresh.consFresh (nb056_alpha_dummy_053) (nb056_alpha_dummy_054 f) (nb056_wpp_notmem_0216) (nb056_wpp_notmem_0217 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0218) (nb056_wpp_notmem_0219 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0118) (nb056_wpp_notmem_0119 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0120) (nb056_wpp_notmem_0121 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0122) (nb056_wpp_notmem_0123 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0124) (nb056_wpp_notmem_0125 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0126) (nb056_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0128) (nb056_wpp_notmem_0129 f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))

noncomputable def nb056_wpp_refl_0013 (f : Var) : TReflOn [((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0013 f)

noncomputable def nb056_split_alpha_0009 (f : Var) : TAlphaWff [((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_079)) (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_079)) (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_080 f)) (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_080 f)) (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0075 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0071) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0073 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0008 f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0008 f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (nb056_wpp_refl_0013 f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0075 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0071) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0073 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0008 f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0008 f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (nb056_wpp_refl_0013 f)))))))))))))))))))

theorem nb056_compact_fv_empty_0066 : (nb056_alpha_dummy_107) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0220 : (nb056_alpha_dummy_107) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_107, fv_syn_c1c] using (nb056_compact_fv_empty_0066)

theorem nb056_compact_fv_empty_0067 (f : Var) : (nb056_alpha_dummy_110 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0221 (f : Var) : (nb056_alpha_dummy_110 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_110, fv_syn_c1c] using (nb056_compact_fv_empty_0067 f)

theorem nb056_compact_fv_empty_0068 : (nb056_alpha_dummy_106) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0222 : (nb056_alpha_dummy_106) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_106, fv_syn_c1c] using (nb056_compact_fv_empty_0068)

theorem nb056_compact_fv_empty_0069 (f : Var) : (nb056_alpha_dummy_109 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0223 (f : Var) : (nb056_alpha_dummy_109 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_109, fv_syn_c1c] using (nb056_compact_fv_empty_0069 f)

theorem nb056_compact_fv_empty_0070 : (nb056_alpha_dummy_105) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0224 : (nb056_alpha_dummy_105) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_105, fv_syn_c1c] using (nb056_compact_fv_empty_0070)

theorem nb056_compact_fv_empty_0071 (f : Var) : (nb056_alpha_dummy_108 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0225 (f : Var) : (nb056_alpha_dummy_108 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_108, fv_syn_c1c] using (nb056_compact_fv_empty_0071 f)

theorem nb056_compact_fv_empty_0072 : (nb056_alpha_dummy_103) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0226 : (nb056_alpha_dummy_103) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_103, fv_syn_c1c] using (nb056_compact_fv_empty_0072)

theorem nb056_compact_fv_empty_0073 (f : Var) : (nb056_alpha_dummy_104 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0227 (f : Var) : (nb056_alpha_dummy_104 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_104, fv_syn_c1c] using (nb056_compact_fv_empty_0073 f)

theorem nb056_compact_fv_empty_0074 : (nb056_alpha_dummy_099) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0228 : (nb056_alpha_dummy_099) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_099, fv_syn_c1c] using (nb056_compact_fv_empty_0074)

theorem nb056_compact_fv_empty_0075 (f : Var) : (nb056_alpha_dummy_101 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0229 (f : Var) : (nb056_alpha_dummy_101 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_101, fv_syn_c1c] using (nb056_compact_fv_empty_0075 f)

theorem nb056_compact_fv_empty_0076 : (nb056_alpha_dummy_100) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0230 : (nb056_alpha_dummy_100) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_100, fv_syn_c1c] using (nb056_compact_fv_empty_0076)

theorem nb056_compact_fv_empty_0077 (f : Var) : (nb056_alpha_dummy_102 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0231 (f : Var) : (nb056_alpha_dummy_102 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_102, fv_syn_c1c] using (nb056_compact_fv_empty_0077 f)

theorem nb056_compact_fv_empty_0078 : (nb056_alpha_dummy_092) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0232 : (nb056_alpha_dummy_092) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_092, fv_syn_c1c] using (nb056_compact_fv_empty_0078)

theorem nb056_compact_fv_empty_0079 (f : Var) : (nb056_alpha_dummy_094 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0233 (f : Var) : (nb056_alpha_dummy_094 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_094, fv_syn_c1c] using (nb056_compact_fv_empty_0079 f)

theorem nb056_compact_fv_empty_0080 : (nb056_alpha_dummy_091) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0234 : (nb056_alpha_dummy_091) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_091, fv_syn_c1c] using (nb056_compact_fv_empty_0080)

theorem nb056_compact_fv_empty_0081 (f : Var) : (nb056_alpha_dummy_093 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0235 (f : Var) : (nb056_alpha_dummy_093 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_093, fv_syn_c1c] using (nb056_compact_fv_empty_0081 f)

theorem nb056_compact_fv_empty_0082 : (nb056_alpha_dummy_097) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0236 : (nb056_alpha_dummy_097) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_097, fv_syn_c1c] using (nb056_compact_fv_empty_0082)

theorem nb056_compact_fv_empty_0083 (f : Var) : (nb056_alpha_dummy_098 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0237 (f : Var) : (nb056_alpha_dummy_098 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_098, fv_syn_c1c] using (nb056_compact_fv_empty_0083 f)

theorem nb056_compact_fv_empty_0084 : (nb056_alpha_dummy_095) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0238 : (nb056_alpha_dummy_095) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_095, fv_syn_c1c] using (nb056_compact_fv_empty_0084)

theorem nb056_compact_fv_empty_0085 (f : Var) : (nb056_alpha_dummy_096 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0239 (f : Var) : (nb056_alpha_dummy_096 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_096, fv_syn_c1c] using (nb056_compact_fv_empty_0085 f)

theorem nb056_compact_fv_empty_0086 : (nb056_alpha_dummy_086) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0240 : (nb056_alpha_dummy_086) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_086, fv_syn_c1c] using (nb056_compact_fv_empty_0086)

theorem nb056_compact_fv_empty_0087 (f : Var) : (nb056_alpha_dummy_088 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0241 (f : Var) : (nb056_alpha_dummy_088 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_088, fv_syn_c1c] using (nb056_compact_fv_empty_0087 f)

theorem nb056_compact_fv_empty_0088 : (nb056_alpha_dummy_085) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0242 : (nb056_alpha_dummy_085) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_085, fv_syn_c1c] using (nb056_compact_fv_empty_0088)

theorem nb056_compact_fv_empty_0089 (f : Var) : (nb056_alpha_dummy_087 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0243 (f : Var) : (nb056_alpha_dummy_087 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_087, fv_syn_c1c] using (nb056_compact_fv_empty_0089 f)

theorem nb056_compact_fv_empty_0090 : (nb056_alpha_dummy_089) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0244 : (nb056_alpha_dummy_089) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_089, fv_syn_c1c] using (nb056_compact_fv_empty_0090)

theorem nb056_compact_fv_empty_0091 (f : Var) : (nb056_alpha_dummy_090 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0245 (f : Var) : (nb056_alpha_dummy_090 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_090, fv_syn_c1c] using (nb056_compact_fv_empty_0091 f)

theorem nb056_compact_envfresh_0014 (f : Var) : TEnvFresh [((nb056_alpha_dummy_107), (nb056_alpha_dummy_110 f)), ((nb056_alpha_dummy_106), (nb056_alpha_dummy_109 f)), ((nb056_alpha_dummy_105), (nb056_alpha_dummy_108 f)), ((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)), ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)), ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_097), (nb056_alpha_dummy_098 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_107) (nb056_alpha_dummy_110 f) (nb056_wpp_notmem_0220) (nb056_wpp_notmem_0221 f) (TEnvFresh.consFresh (nb056_alpha_dummy_106) (nb056_alpha_dummy_109 f) (nb056_wpp_notmem_0222) (nb056_wpp_notmem_0223 f) (TEnvFresh.consFresh (nb056_alpha_dummy_105) (nb056_alpha_dummy_108 f) (nb056_wpp_notmem_0224) (nb056_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb056_alpha_dummy_103) (nb056_alpha_dummy_104 f) (nb056_wpp_notmem_0226) (nb056_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb056_alpha_dummy_099) (nb056_alpha_dummy_101 f) (nb056_wpp_notmem_0228) (nb056_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb056_alpha_dummy_100) (nb056_alpha_dummy_102 f) (nb056_wpp_notmem_0230) (nb056_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb056_alpha_dummy_092) (nb056_alpha_dummy_094 f) (nb056_wpp_notmem_0232) (nb056_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb056_alpha_dummy_091) (nb056_alpha_dummy_093 f) (nb056_wpp_notmem_0234) (nb056_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb056_alpha_dummy_097) (nb056_alpha_dummy_098 f) (nb056_wpp_notmem_0236) (nb056_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb056_alpha_dummy_095) (nb056_alpha_dummy_096 f) (nb056_wpp_notmem_0238) (nb056_wpp_notmem_0239 f) (TEnvFresh.consFresh (nb056_alpha_dummy_086) (nb056_alpha_dummy_088 f) (nb056_wpp_notmem_0240) (nb056_wpp_notmem_0241 f) (TEnvFresh.consFresh (nb056_alpha_dummy_085) (nb056_alpha_dummy_087 f) (nb056_wpp_notmem_0242) (nb056_wpp_notmem_0243 f) (TEnvFresh.consFresh (nb056_alpha_dummy_089) (nb056_alpha_dummy_090 f) (nb056_wpp_notmem_0244) (nb056_wpp_notmem_0245 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0150) (nb056_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0020) (nb056_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0022) (nb056_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0024) (nb056_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0026) (nb056_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0028) (nb056_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0030) (nb056_wpp_notmem_0031 f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb056_wpp_refl_0014 (f : Var) : TReflOn [((nb056_alpha_dummy_107), (nb056_alpha_dummy_110 f)), ((nb056_alpha_dummy_106), (nb056_alpha_dummy_109 f)), ((nb056_alpha_dummy_105), (nb056_alpha_dummy_108 f)), ((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)), ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)), ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)), ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)), ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)), ((nb056_alpha_dummy_097), (nb056_alpha_dummy_098 f)), ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)), ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0014 f)

theorem nb056_wpp_notmem_0246 : (nb056_alpha_dummy_107) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_107, fv_syn_c0] using (nb056_compact_fv_empty_0066)

theorem nb056_wpp_notmem_0247 (f : Var) : (nb056_alpha_dummy_110 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_110, fv_syn_c0] using (nb056_compact_fv_empty_0067 f)

theorem nb056_wpp_notmem_0248 : (nb056_alpha_dummy_106) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_106, fv_syn_c0] using (nb056_compact_fv_empty_0068)

theorem nb056_wpp_notmem_0249 (f : Var) : (nb056_alpha_dummy_109 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_109, fv_syn_c0] using (nb056_compact_fv_empty_0069 f)

theorem nb056_wpp_notmem_0250 : (nb056_alpha_dummy_105) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_105, fv_syn_c0] using (nb056_compact_fv_empty_0070)

theorem nb056_wpp_notmem_0251 (f : Var) : (nb056_alpha_dummy_108 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_108, fv_syn_c0] using (nb056_compact_fv_empty_0071 f)

theorem nb056_wpp_notmem_0252 : (nb056_alpha_dummy_103) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_103, fv_syn_c0] using (nb056_compact_fv_empty_0072)

theorem nb056_wpp_notmem_0253 (f : Var) : (nb056_alpha_dummy_104 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_104, fv_syn_c0] using (nb056_compact_fv_empty_0073 f)

theorem nb056_wpp_notmem_0254 : (nb056_alpha_dummy_099) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_099, fv_syn_c0] using (nb056_compact_fv_empty_0074)

theorem nb056_wpp_notmem_0255 (f : Var) : (nb056_alpha_dummy_101 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_101, fv_syn_c0] using (nb056_compact_fv_empty_0075 f)

theorem nb056_wpp_notmem_0256 : (nb056_alpha_dummy_100) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_100, fv_syn_c0] using (nb056_compact_fv_empty_0076)

theorem nb056_wpp_notmem_0257 (f : Var) : (nb056_alpha_dummy_102 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_102, fv_syn_c0] using (nb056_compact_fv_empty_0077 f)

theorem nb056_wpp_notmem_0258 : (nb056_alpha_dummy_092) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_092, fv_syn_c0] using (nb056_compact_fv_empty_0078)

theorem nb056_wpp_notmem_0259 (f : Var) : (nb056_alpha_dummy_094 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_094, fv_syn_c0] using (nb056_compact_fv_empty_0079 f)

theorem nb056_wpp_notmem_0260 : (nb056_alpha_dummy_091) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_091, fv_syn_c0] using (nb056_compact_fv_empty_0080)

theorem nb056_wpp_notmem_0261 (f : Var) : (nb056_alpha_dummy_093 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_093, fv_syn_c0] using (nb056_compact_fv_empty_0081 f)

theorem nb056_wpp_notmem_0262 : (nb056_alpha_dummy_097) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_097, fv_syn_c0] using (nb056_compact_fv_empty_0082)

theorem nb056_wpp_notmem_0263 (f : Var) : (nb056_alpha_dummy_098 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_098, fv_syn_c0] using (nb056_compact_fv_empty_0083 f)

theorem nb056_wpp_notmem_0264 : (nb056_alpha_dummy_095) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_095, fv_syn_c0] using (nb056_compact_fv_empty_0084)

theorem nb056_wpp_notmem_0265 (f : Var) : (nb056_alpha_dummy_096 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_096, fv_syn_c0] using (nb056_compact_fv_empty_0085 f)

theorem nb056_wpp_notmem_0266 : (nb056_alpha_dummy_086) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_086, fv_syn_c0] using (nb056_compact_fv_empty_0086)

theorem nb056_wpp_notmem_0267 (f : Var) : (nb056_alpha_dummy_088 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_088, fv_syn_c0] using (nb056_compact_fv_empty_0087 f)

theorem nb056_wpp_notmem_0268 : (nb056_alpha_dummy_085) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_085, fv_syn_c0] using (nb056_compact_fv_empty_0088)

theorem nb056_wpp_notmem_0269 (f : Var) : (nb056_alpha_dummy_087 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_087, fv_syn_c0] using (nb056_compact_fv_empty_0089 f)

theorem nb056_wpp_notmem_0270 : (nb056_alpha_dummy_089) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_089, fv_syn_c0] using (nb056_compact_fv_empty_0090)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
