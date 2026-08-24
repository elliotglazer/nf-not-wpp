import NAR4C057C001Part008

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

theorem nb057_compact_envfresh_0007 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_068) (nb057_alpha_dummy_071 f) (nb057_wpp_notmem_0106) (nb057_wpp_notmem_0107 f) (TEnvFresh.consFresh (nb057_alpha_dummy_067) (nb057_alpha_dummy_070 f) (nb057_wpp_notmem_0108) (nb057_wpp_notmem_0109 f) (TEnvFresh.consFresh (nb057_alpha_dummy_066) (nb057_alpha_dummy_069 f) (nb057_wpp_notmem_0110) (nb057_wpp_notmem_0111 f) (TEnvFresh.consFresh (nb057_alpha_dummy_064) (nb057_alpha_dummy_065 f) (nb057_wpp_notmem_0112) (nb057_wpp_notmem_0113 f) (TEnvFresh.consFresh (nb057_alpha_dummy_060) (nb057_alpha_dummy_062 f) (nb057_wpp_notmem_0114) (nb057_wpp_notmem_0115 f) (TEnvFresh.consFresh (nb057_alpha_dummy_061) (nb057_alpha_dummy_063 f) (nb057_wpp_notmem_0116) (nb057_wpp_notmem_0117 f) (TEnvFresh.consFresh (nb057_alpha_dummy_053) (nb057_alpha_dummy_055 f) (nb057_wpp_notmem_0118) (nb057_wpp_notmem_0119 f) (TEnvFresh.consFresh (nb057_alpha_dummy_052) (nb057_alpha_dummy_054 f) (nb057_wpp_notmem_0120) (nb057_wpp_notmem_0121 f) (TEnvFresh.consFresh (nb057_alpha_dummy_058) (nb057_alpha_dummy_059 f) (nb057_wpp_notmem_0122) (nb057_wpp_notmem_0123 f) (TEnvFresh.consFresh (nb057_alpha_dummy_056) (nb057_alpha_dummy_057 f) (nb057_wpp_notmem_0124) (nb057_wpp_notmem_0125 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0126) (nb057_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0128) (nb057_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0130) (nb057_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0132) (nb057_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0134) (nb057_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb057_wpp_refl_0007 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0007 f a)

theorem nb057_wpp_notmem_0136 : (nb057_alpha_dummy_068) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_068, fv_syn_c0] using (nb057_compact_fv_empty_0032)

theorem nb057_wpp_notmem_0137 (f : Var) : (nb057_alpha_dummy_071 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_071, fv_syn_c0] using (nb057_compact_fv_empty_0033 f)

theorem nb057_wpp_notmem_0138 : (nb057_alpha_dummy_067) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_067, fv_syn_c0] using (nb057_compact_fv_empty_0034)

theorem nb057_wpp_notmem_0139 (f : Var) : (nb057_alpha_dummy_070 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_070, fv_syn_c0] using (nb057_compact_fv_empty_0035 f)

theorem nb057_wpp_notmem_0140 : (nb057_alpha_dummy_066) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_066, fv_syn_c0] using (nb057_compact_fv_empty_0036)

theorem nb057_wpp_notmem_0141 (f : Var) : (nb057_alpha_dummy_069 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_069, fv_syn_c0] using (nb057_compact_fv_empty_0037 f)

theorem nb057_wpp_notmem_0142 : (nb057_alpha_dummy_064) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_064, fv_syn_c0] using (nb057_compact_fv_empty_0038)

theorem nb057_wpp_notmem_0143 (f : Var) : (nb057_alpha_dummy_065 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_065, fv_syn_c0] using (nb057_compact_fv_empty_0039 f)

theorem nb057_wpp_notmem_0144 : (nb057_alpha_dummy_060) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_060, fv_syn_c0] using (nb057_compact_fv_empty_0040)

theorem nb057_wpp_notmem_0145 (f : Var) : (nb057_alpha_dummy_062 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_062, fv_syn_c0] using (nb057_compact_fv_empty_0041 f)

theorem nb057_wpp_notmem_0146 : (nb057_alpha_dummy_061) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_061, fv_syn_c0] using (nb057_compact_fv_empty_0042)

theorem nb057_wpp_notmem_0147 (f : Var) : (nb057_alpha_dummy_063 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_063, fv_syn_c0] using (nb057_compact_fv_empty_0043 f)

theorem nb057_wpp_notmem_0148 : (nb057_alpha_dummy_053) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_053, fv_syn_c0] using (nb057_compact_fv_empty_0044)

theorem nb057_wpp_notmem_0149 (f : Var) : (nb057_alpha_dummy_055 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_055, fv_syn_c0] using (nb057_compact_fv_empty_0045 f)

theorem nb057_wpp_notmem_0150 : (nb057_alpha_dummy_052) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_052, fv_syn_c0] using (nb057_compact_fv_empty_0046)

theorem nb057_wpp_notmem_0151 (f : Var) : (nb057_alpha_dummy_054 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_054, fv_syn_c0] using (nb057_compact_fv_empty_0047 f)

theorem nb057_wpp_notmem_0152 : (nb057_alpha_dummy_058) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_058, fv_syn_c0] using (nb057_compact_fv_empty_0048)

theorem nb057_wpp_notmem_0153 (f : Var) : (nb057_alpha_dummy_059 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_059, fv_syn_c0] using (nb057_compact_fv_empty_0049 f)

theorem nb057_wpp_notmem_0154 : (nb057_alpha_dummy_056) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_056, fv_syn_c0] using (nb057_compact_fv_empty_0050)

theorem nb057_wpp_notmem_0155 (f : Var) : (nb057_alpha_dummy_057 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_057, fv_syn_c0] using (nb057_compact_fv_empty_0051 f)

theorem nb057_wpp_notmem_0156 : (nb057_alpha_dummy_045) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_045, fv_syn_c0] using (nb057_compact_fv_empty_0052)

theorem nb057_wpp_notmem_0157 (f : Var) : (nb057_alpha_dummy_048 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_048, fv_syn_c0] using (nb057_compact_fv_empty_0053 f)

theorem nb057_wpp_notmem_0158 : (nb057_alpha_dummy_044) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_044, fv_syn_c0] using (nb057_compact_fv_empty_0054)

theorem nb057_wpp_notmem_0159 (f : Var) : (nb057_alpha_dummy_047 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_047, fv_syn_c0] using (nb057_compact_fv_empty_0055 f)

theorem nb057_wpp_notmem_0160 : (nb057_alpha_dummy_050) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_050, fv_syn_c0] using (nb057_compact_fv_empty_0056)

theorem nb057_wpp_notmem_0161 (f : Var) : (nb057_alpha_dummy_051 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_051, fv_syn_c0] using (nb057_compact_fv_empty_0057 f)

theorem nb057_wpp_notmem_0162 : (nb057_alpha_dummy_042) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_042, fv_syn_c0] using (nb057_compact_fv_empty_0058)

theorem nb057_wpp_notmem_0163 (f : Var) : (nb057_alpha_dummy_043 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_043, fv_syn_c0] using (nb057_compact_fv_empty_0059 f)

theorem nb057_wpp_notmem_0164 : (nb057_alpha_dummy_040) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_040, fv_syn_c0] using (nb057_compact_fv_empty_0060)

theorem nb057_wpp_notmem_0165 (f : Var) : (nb057_alpha_dummy_041 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_041, fv_syn_c0] using (nb057_compact_fv_empty_0061 f)

theorem nb057_compact_envfresh_0008 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_068) (nb057_alpha_dummy_071 f) (nb057_wpp_notmem_0136) (nb057_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb057_alpha_dummy_067) (nb057_alpha_dummy_070 f) (nb057_wpp_notmem_0138) (nb057_wpp_notmem_0139 f) (TEnvFresh.consFresh (nb057_alpha_dummy_066) (nb057_alpha_dummy_069 f) (nb057_wpp_notmem_0140) (nb057_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb057_alpha_dummy_064) (nb057_alpha_dummy_065 f) (nb057_wpp_notmem_0142) (nb057_wpp_notmem_0143 f) (TEnvFresh.consFresh (nb057_alpha_dummy_060) (nb057_alpha_dummy_062 f) (nb057_wpp_notmem_0144) (nb057_wpp_notmem_0145 f) (TEnvFresh.consFresh (nb057_alpha_dummy_061) (nb057_alpha_dummy_063 f) (nb057_wpp_notmem_0146) (nb057_wpp_notmem_0147 f) (TEnvFresh.consFresh (nb057_alpha_dummy_053) (nb057_alpha_dummy_055 f) (nb057_wpp_notmem_0148) (nb057_wpp_notmem_0149 f) (TEnvFresh.consFresh (nb057_alpha_dummy_052) (nb057_alpha_dummy_054 f) (nb057_wpp_notmem_0150) (nb057_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb057_alpha_dummy_058) (nb057_alpha_dummy_059 f) (nb057_wpp_notmem_0152) (nb057_wpp_notmem_0153 f) (TEnvFresh.consFresh (nb057_alpha_dummy_056) (nb057_alpha_dummy_057 f) (nb057_wpp_notmem_0154) (nb057_wpp_notmem_0155 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0156) (nb057_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0158) (nb057_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0160) (nb057_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0162) (nb057_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0164) (nb057_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb057_wpp_refl_0008 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0008 f a)

noncomputable def nb057_split_alpha_0005 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_066)) (syn_cun (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_069 f)) (syn_cun (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0059 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0059 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0008 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0073 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0071 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0073 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0071 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0166 : (nb057_alpha_dummy_064) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_064, fv_syn_cnnc] using (nb057_compact_fv_empty_0038)

theorem nb057_wpp_notmem_0167 (f : Var) : (nb057_alpha_dummy_065 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_065, fv_syn_cnnc] using (nb057_compact_fv_empty_0039 f)

theorem nb057_wpp_notmem_0168 : (nb057_alpha_dummy_060) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_060, fv_syn_cnnc] using (nb057_compact_fv_empty_0040)

theorem nb057_wpp_notmem_0169 (f : Var) : (nb057_alpha_dummy_062 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_062, fv_syn_cnnc] using (nb057_compact_fv_empty_0041 f)

theorem nb057_wpp_notmem_0170 : (nb057_alpha_dummy_061) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_061, fv_syn_cnnc] using (nb057_compact_fv_empty_0042)

theorem nb057_wpp_notmem_0171 (f : Var) : (nb057_alpha_dummy_063 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_063, fv_syn_cnnc] using (nb057_compact_fv_empty_0043 f)

theorem nb057_wpp_notmem_0172 : (nb057_alpha_dummy_053) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_053, fv_syn_cnnc] using (nb057_compact_fv_empty_0044)

theorem nb057_wpp_notmem_0173 (f : Var) : (nb057_alpha_dummy_055 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_055, fv_syn_cnnc] using (nb057_compact_fv_empty_0045 f)

theorem nb057_wpp_notmem_0174 : (nb057_alpha_dummy_052) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_052, fv_syn_cnnc] using (nb057_compact_fv_empty_0046)

theorem nb057_wpp_notmem_0175 (f : Var) : (nb057_alpha_dummy_054 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_054, fv_syn_cnnc] using (nb057_compact_fv_empty_0047 f)

theorem nb057_wpp_notmem_0176 : (nb057_alpha_dummy_058) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_058, fv_syn_cnnc] using (nb057_compact_fv_empty_0048)

theorem nb057_wpp_notmem_0177 (f : Var) : (nb057_alpha_dummy_059 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_059, fv_syn_cnnc] using (nb057_compact_fv_empty_0049 f)

theorem nb057_wpp_notmem_0178 : (nb057_alpha_dummy_056) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_056, fv_syn_cnnc] using (nb057_compact_fv_empty_0050)

theorem nb057_wpp_notmem_0179 (f : Var) : (nb057_alpha_dummy_057 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_057, fv_syn_cnnc] using (nb057_compact_fv_empty_0051 f)

theorem nb057_wpp_notmem_0180 : (nb057_alpha_dummy_045) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_045, fv_syn_cnnc] using (nb057_compact_fv_empty_0052)

theorem nb057_wpp_notmem_0181 (f : Var) : (nb057_alpha_dummy_048 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_048, fv_syn_cnnc] using (nb057_compact_fv_empty_0053 f)

theorem nb057_wpp_notmem_0182 : (nb057_alpha_dummy_044) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_044, fv_syn_cnnc] using (nb057_compact_fv_empty_0054)

theorem nb057_wpp_notmem_0183 (f : Var) : (nb057_alpha_dummy_047 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_047, fv_syn_cnnc] using (nb057_compact_fv_empty_0055 f)

theorem nb057_wpp_notmem_0184 : (nb057_alpha_dummy_050) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_050, fv_syn_cnnc] using (nb057_compact_fv_empty_0056)

theorem nb057_wpp_notmem_0185 (f : Var) : (nb057_alpha_dummy_051 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_051, fv_syn_cnnc] using (nb057_compact_fv_empty_0057 f)

theorem nb057_wpp_notmem_0186 : (nb057_alpha_dummy_042) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_042, fv_syn_cnnc] using (nb057_compact_fv_empty_0058)

theorem nb057_wpp_notmem_0187 (f : Var) : (nb057_alpha_dummy_043 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_043, fv_syn_cnnc] using (nb057_compact_fv_empty_0059 f)

theorem nb057_wpp_notmem_0188 : (nb057_alpha_dummy_040) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_040, fv_syn_cnnc] using (nb057_compact_fv_empty_0060)

theorem nb057_wpp_notmem_0189 (f : Var) : (nb057_alpha_dummy_041 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_041, fv_syn_cnnc] using (nb057_compact_fv_empty_0061 f)

theorem nb057_compact_envfresh_0009 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_064) (nb057_alpha_dummy_065 f) (nb057_wpp_notmem_0166) (nb057_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb057_alpha_dummy_060) (nb057_alpha_dummy_062 f) (nb057_wpp_notmem_0168) (nb057_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb057_alpha_dummy_061) (nb057_alpha_dummy_063 f) (nb057_wpp_notmem_0170) (nb057_wpp_notmem_0171 f) (TEnvFresh.consFresh (nb057_alpha_dummy_053) (nb057_alpha_dummy_055 f) (nb057_wpp_notmem_0172) (nb057_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb057_alpha_dummy_052) (nb057_alpha_dummy_054 f) (nb057_wpp_notmem_0174) (nb057_wpp_notmem_0175 f) (TEnvFresh.consFresh (nb057_alpha_dummy_058) (nb057_alpha_dummy_059 f) (nb057_wpp_notmem_0176) (nb057_wpp_notmem_0177 f) (TEnvFresh.consFresh (nb057_alpha_dummy_056) (nb057_alpha_dummy_057 f) (nb057_wpp_notmem_0178) (nb057_wpp_notmem_0179 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0180) (nb057_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0182) (nb057_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0184) (nb057_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0186) (nb057_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0188) (nb057_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb057_wpp_refl_0009 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0009 f a)

noncomputable def nb057_split_alpha_0006 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053)))) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_053))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_055 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0056) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0057 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0007 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0005 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0009 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0009 f a))))))))))))))))))

theorem nb057_compact_fv_empty_0062 : (nb057_alpha_dummy_086) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0190 : (nb057_alpha_dummy_086) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_086, fv_syn_c1c] using (nb057_compact_fv_empty_0062)

theorem nb057_compact_fv_empty_0063 (f : Var) : (nb057_alpha_dummy_087 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0191 (f : Var) : (nb057_alpha_dummy_087 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_087, fv_syn_c1c] using (nb057_compact_fv_empty_0063 f)

theorem nb057_compact_fv_empty_0064 : (nb057_alpha_dummy_084) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0192 : (nb057_alpha_dummy_084) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_084, fv_syn_c1c] using (nb057_compact_fv_empty_0064)

theorem nb057_compact_fv_empty_0065 (f : Var) : (nb057_alpha_dummy_085 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0193 (f : Var) : (nb057_alpha_dummy_085 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_085, fv_syn_c1c] using (nb057_compact_fv_empty_0065 f)

theorem nb057_compact_fv_empty_0066 : (nb057_alpha_dummy_082) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0194 : (nb057_alpha_dummy_082) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_082, fv_syn_c1c] using (nb057_compact_fv_empty_0066)

theorem nb057_compact_fv_empty_0067 (f : Var) : (nb057_alpha_dummy_083 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0195 (f : Var) : (nb057_alpha_dummy_083 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_083, fv_syn_c1c] using (nb057_compact_fv_empty_0067 f)

theorem nb057_compact_envfresh_0010 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_068) (nb057_alpha_dummy_071 f) (nb057_wpp_notmem_0106) (nb057_wpp_notmem_0107 f) (TEnvFresh.consFresh (nb057_alpha_dummy_067) (nb057_alpha_dummy_070 f) (nb057_wpp_notmem_0108) (nb057_wpp_notmem_0109 f) (TEnvFresh.consFresh (nb057_alpha_dummy_066) (nb057_alpha_dummy_069 f) (nb057_wpp_notmem_0110) (nb057_wpp_notmem_0111 f) (TEnvFresh.consFresh (nb057_alpha_dummy_064) (nb057_alpha_dummy_065 f) (nb057_wpp_notmem_0112) (nb057_wpp_notmem_0113 f) (TEnvFresh.consFresh (nb057_alpha_dummy_060) (nb057_alpha_dummy_062 f) (nb057_wpp_notmem_0114) (nb057_wpp_notmem_0115 f) (TEnvFresh.consFresh (nb057_alpha_dummy_061) (nb057_alpha_dummy_063 f) (nb057_wpp_notmem_0116) (nb057_wpp_notmem_0117 f) (TEnvFresh.consFresh (nb057_alpha_dummy_086) (nb057_alpha_dummy_087 f) (nb057_wpp_notmem_0190) (nb057_wpp_notmem_0191 f) (TEnvFresh.consFresh (nb057_alpha_dummy_084) (nb057_alpha_dummy_085 f) (nb057_wpp_notmem_0192) (nb057_wpp_notmem_0193 f) (TEnvFresh.consFresh (nb057_alpha_dummy_053) (nb057_alpha_dummy_055 f) (nb057_wpp_notmem_0118) (nb057_wpp_notmem_0119 f) (TEnvFresh.consFresh (nb057_alpha_dummy_052) (nb057_alpha_dummy_054 f) (nb057_wpp_notmem_0120) (nb057_wpp_notmem_0121 f) (TEnvFresh.consFresh (nb057_alpha_dummy_082) (nb057_alpha_dummy_083 f) (nb057_wpp_notmem_0194) (nb057_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb057_alpha_dummy_056) (nb057_alpha_dummy_057 f) (nb057_wpp_notmem_0124) (nb057_wpp_notmem_0125 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0126) (nb057_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0128) (nb057_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0130) (nb057_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0132) (nb057_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0134) (nb057_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb057_wpp_refl_0010 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0010 f a)

theorem nb057_wpp_notmem_0196 : (nb057_alpha_dummy_086) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_086, fv_syn_c0] using (nb057_compact_fv_empty_0062)

theorem nb057_wpp_notmem_0197 (f : Var) : (nb057_alpha_dummy_087 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_087, fv_syn_c0] using (nb057_compact_fv_empty_0063 f)

theorem nb057_wpp_notmem_0198 : (nb057_alpha_dummy_084) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_084, fv_syn_c0] using (nb057_compact_fv_empty_0064)

theorem nb057_wpp_notmem_0199 (f : Var) : (nb057_alpha_dummy_085 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_085, fv_syn_c0] using (nb057_compact_fv_empty_0065 f)

theorem nb057_wpp_notmem_0200 : (nb057_alpha_dummy_082) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_082, fv_syn_c0] using (nb057_compact_fv_empty_0066)

theorem nb057_wpp_notmem_0201 (f : Var) : (nb057_alpha_dummy_083 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_083, fv_syn_c0] using (nb057_compact_fv_empty_0067 f)

theorem nb057_compact_envfresh_0011 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_068) (nb057_alpha_dummy_071 f) (nb057_wpp_notmem_0136) (nb057_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb057_alpha_dummy_067) (nb057_alpha_dummy_070 f) (nb057_wpp_notmem_0138) (nb057_wpp_notmem_0139 f) (TEnvFresh.consFresh (nb057_alpha_dummy_066) (nb057_alpha_dummy_069 f) (nb057_wpp_notmem_0140) (nb057_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb057_alpha_dummy_064) (nb057_alpha_dummy_065 f) (nb057_wpp_notmem_0142) (nb057_wpp_notmem_0143 f) (TEnvFresh.consFresh (nb057_alpha_dummy_060) (nb057_alpha_dummy_062 f) (nb057_wpp_notmem_0144) (nb057_wpp_notmem_0145 f) (TEnvFresh.consFresh (nb057_alpha_dummy_061) (nb057_alpha_dummy_063 f) (nb057_wpp_notmem_0146) (nb057_wpp_notmem_0147 f) (TEnvFresh.consFresh (nb057_alpha_dummy_086) (nb057_alpha_dummy_087 f) (nb057_wpp_notmem_0196) (nb057_wpp_notmem_0197 f) (TEnvFresh.consFresh (nb057_alpha_dummy_084) (nb057_alpha_dummy_085 f) (nb057_wpp_notmem_0198) (nb057_wpp_notmem_0199 f) (TEnvFresh.consFresh (nb057_alpha_dummy_053) (nb057_alpha_dummy_055 f) (nb057_wpp_notmem_0148) (nb057_wpp_notmem_0149 f) (TEnvFresh.consFresh (nb057_alpha_dummy_052) (nb057_alpha_dummy_054 f) (nb057_wpp_notmem_0150) (nb057_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb057_alpha_dummy_082) (nb057_alpha_dummy_083 f) (nb057_wpp_notmem_0200) (nb057_wpp_notmem_0201 f) (TEnvFresh.consFresh (nb057_alpha_dummy_056) (nb057_alpha_dummy_057 f) (nb057_wpp_notmem_0154) (nb057_wpp_notmem_0155 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0156) (nb057_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0158) (nb057_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0160) (nb057_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0162) (nb057_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0164) (nb057_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb057_wpp_refl_0011 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0011 f a)

noncomputable def nb057_split_alpha_0007 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_066)) (syn_cun (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_069 f)) (syn_cun (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0059 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0059 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0011 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0073 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0071 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0073 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0071 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0202 : (nb057_alpha_dummy_086) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_086, fv_syn_cnnc] using (nb057_compact_fv_empty_0062)

theorem nb057_wpp_notmem_0203 (f : Var) : (nb057_alpha_dummy_087 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_087, fv_syn_cnnc] using (nb057_compact_fv_empty_0063 f)

theorem nb057_wpp_notmem_0204 : (nb057_alpha_dummy_084) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_084, fv_syn_cnnc] using (nb057_compact_fv_empty_0064)

theorem nb057_wpp_notmem_0205 (f : Var) : (nb057_alpha_dummy_085 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_085, fv_syn_cnnc] using (nb057_compact_fv_empty_0065 f)

theorem nb057_wpp_notmem_0206 : (nb057_alpha_dummy_082) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_082, fv_syn_cnnc] using (nb057_compact_fv_empty_0066)

theorem nb057_wpp_notmem_0207 (f : Var) : (nb057_alpha_dummy_083 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_083, fv_syn_cnnc] using (nb057_compact_fv_empty_0067 f)

theorem nb057_compact_envfresh_0012 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_064) (nb057_alpha_dummy_065 f) (nb057_wpp_notmem_0166) (nb057_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb057_alpha_dummy_060) (nb057_alpha_dummy_062 f) (nb057_wpp_notmem_0168) (nb057_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb057_alpha_dummy_061) (nb057_alpha_dummy_063 f) (nb057_wpp_notmem_0170) (nb057_wpp_notmem_0171 f) (TEnvFresh.consFresh (nb057_alpha_dummy_086) (nb057_alpha_dummy_087 f) (nb057_wpp_notmem_0202) (nb057_wpp_notmem_0203 f) (TEnvFresh.consFresh (nb057_alpha_dummy_084) (nb057_alpha_dummy_085 f) (nb057_wpp_notmem_0204) (nb057_wpp_notmem_0205 f) (TEnvFresh.consFresh (nb057_alpha_dummy_053) (nb057_alpha_dummy_055 f) (nb057_wpp_notmem_0172) (nb057_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb057_alpha_dummy_052) (nb057_alpha_dummy_054 f) (nb057_wpp_notmem_0174) (nb057_wpp_notmem_0175 f) (TEnvFresh.consFresh (nb057_alpha_dummy_082) (nb057_alpha_dummy_083 f) (nb057_wpp_notmem_0206) (nb057_wpp_notmem_0207 f) (TEnvFresh.consFresh (nb057_alpha_dummy_056) (nb057_alpha_dummy_057 f) (nb057_wpp_notmem_0178) (nb057_wpp_notmem_0179 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0180) (nb057_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0182) (nb057_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0184) (nb057_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0186) (nb057_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0188) (nb057_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
