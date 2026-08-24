import NAR4C057C001Part012

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

noncomputable def nb057_split_alpha_0017 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_144)) (syn_cun (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_147 f)) (syn_cun (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0025 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0402 : (nb057_alpha_dummy_164) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_164, fv_syn_cnnc] using (nb057_compact_fv_empty_0122)

theorem nb057_wpp_notmem_0403 (f : Var) : (nb057_alpha_dummy_165 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_165, fv_syn_cnnc] using (nb057_compact_fv_empty_0123 f)

theorem nb057_wpp_notmem_0404 : (nb057_alpha_dummy_162) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_162, fv_syn_cnnc] using (nb057_compact_fv_empty_0124)

theorem nb057_wpp_notmem_0405 (f : Var) : (nb057_alpha_dummy_163 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_163, fv_syn_cnnc] using (nb057_compact_fv_empty_0125 f)

theorem nb057_wpp_notmem_0406 : (nb057_alpha_dummy_160) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_160, fv_syn_cnnc] using (nb057_compact_fv_empty_0126)

theorem nb057_wpp_notmem_0407 (f : Var) : (nb057_alpha_dummy_161 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_161, fv_syn_cnnc] using (nb057_compact_fv_empty_0127 f)

theorem nb057_compact_envfresh_0026 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_142) (nb057_alpha_dummy_143 f) (nb057_wpp_notmem_0370) (nb057_wpp_notmem_0371 f) (TEnvFresh.consFresh (nb057_alpha_dummy_138) (nb057_alpha_dummy_140 f) (nb057_wpp_notmem_0372) (nb057_wpp_notmem_0373 f) (TEnvFresh.consFresh (nb057_alpha_dummy_139) (nb057_alpha_dummy_141 f) (nb057_wpp_notmem_0374) (nb057_wpp_notmem_0375 f) (TEnvFresh.consFresh (nb057_alpha_dummy_164) (nb057_alpha_dummy_165 f) (nb057_wpp_notmem_0402) (nb057_wpp_notmem_0403 f) (TEnvFresh.consFresh (nb057_alpha_dummy_162) (nb057_alpha_dummy_163 f) (nb057_wpp_notmem_0404) (nb057_wpp_notmem_0405 f) (TEnvFresh.consFresh (nb057_alpha_dummy_131) (nb057_alpha_dummy_133 f) (nb057_wpp_notmem_0376) (nb057_wpp_notmem_0377 f) (TEnvFresh.consFresh (nb057_alpha_dummy_130) (nb057_alpha_dummy_132 f) (nb057_wpp_notmem_0378) (nb057_wpp_notmem_0379 f) (TEnvFresh.consFresh (nb057_alpha_dummy_160) (nb057_alpha_dummy_161 f) (nb057_wpp_notmem_0406) (nb057_wpp_notmem_0407 f) (TEnvFresh.consFresh (nb057_alpha_dummy_134) (nb057_alpha_dummy_135 f) (nb057_wpp_notmem_0382) (nb057_wpp_notmem_0383 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0384) (nb057_wpp_notmem_0385 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0386) (nb057_wpp_notmem_0387 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0388) (nb057_wpp_notmem_0389 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0286) (nb057_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0180) (nb057_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0182) (nb057_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0184) (nb057_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0186) (nb057_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0188) (nb057_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))))

noncomputable def nb057_wpp_refl_0026 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0026 f a)

noncomputable def nb057_split_alpha_0018 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.classEq (Class.cv (nb057_alpha_dummy_139)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_138)))) (Wff.classEq (Class.cv (nb057_alpha_dummy_141 f)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_140 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_131))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_133 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0136) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0137 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0137 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)), ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)), ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)), ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0024 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0017 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0026 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)), ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)), ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)), ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)), ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0026 f a))))))))))

theorem nb057_wpp_notmem_0408 : (nb057_alpha_dummy_162) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_162, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0124)

theorem nb057_wpp_notmem_0409 (f : Var) : (nb057_alpha_dummy_163 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_163, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0125 f)

theorem nb057_wpp_notmem_0410 : (nb057_alpha_dummy_131) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_131, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0108)

theorem nb057_wpp_notmem_0411 (f : Var) : (nb057_alpha_dummy_133 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_133, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0109 f)

theorem nb057_wpp_notmem_0412 : (nb057_alpha_dummy_130) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_130, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0110)

theorem nb057_wpp_notmem_0413 (f : Var) : (nb057_alpha_dummy_132 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_132, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0111 f)

theorem nb057_wpp_notmem_0414 : (nb057_alpha_dummy_160) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_160, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0126)

theorem nb057_wpp_notmem_0415 (f : Var) : (nb057_alpha_dummy_161 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_161, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0127 f)

theorem nb057_wpp_notmem_0416 : (nb057_alpha_dummy_134) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_134, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0114)

theorem nb057_wpp_notmem_0417 (f : Var) : (nb057_alpha_dummy_135 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_135, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0115 f)

theorem nb057_wpp_notmem_0418 : (nb057_alpha_dummy_125) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_125, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0116)

theorem nb057_wpp_notmem_0419 (f : Var) : (nb057_alpha_dummy_127 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_127, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0117 f)

theorem nb057_wpp_notmem_0420 : (nb057_alpha_dummy_124) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_124, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0118)

theorem nb057_wpp_notmem_0421 (f : Var) : (nb057_alpha_dummy_126 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_126, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0119 f)

theorem nb057_wpp_notmem_0422 : (nb057_alpha_dummy_128) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_128, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0120)

theorem nb057_wpp_notmem_0423 (f : Var) : (nb057_alpha_dummy_129 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_129, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0121 f)

theorem nb057_compact_envfresh_0027 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_162) (nb057_alpha_dummy_163 f) (nb057_wpp_notmem_0408) (nb057_wpp_notmem_0409 f) (TEnvFresh.consFresh (nb057_alpha_dummy_131) (nb057_alpha_dummy_133 f) (nb057_wpp_notmem_0410) (nb057_wpp_notmem_0411 f) (TEnvFresh.consFresh (nb057_alpha_dummy_130) (nb057_alpha_dummy_132 f) (nb057_wpp_notmem_0412) (nb057_wpp_notmem_0413 f) (TEnvFresh.consFresh (nb057_alpha_dummy_160) (nb057_alpha_dummy_161 f) (nb057_wpp_notmem_0414) (nb057_wpp_notmem_0415 f) (TEnvFresh.consFresh (nb057_alpha_dummy_134) (nb057_alpha_dummy_135 f) (nb057_wpp_notmem_0416) (nb057_wpp_notmem_0417 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0418) (nb057_wpp_notmem_0419 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0420) (nb057_wpp_notmem_0421 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0422) (nb057_wpp_notmem_0423 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0316) (nb057_wpp_notmem_0317 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0218) (nb057_wpp_notmem_0219 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0220) (nb057_wpp_notmem_0221 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0222) (nb057_wpp_notmem_0223 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0224) (nb057_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0226) (nb057_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0100) (nb057_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0102) (nb057_wpp_notmem_0103 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0104) (nb057_wpp_notmem_0105 f a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))

noncomputable def nb057_wpp_refl_0027 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0027 f a)

noncomputable def nb057_split_alpha_0019 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_160)) (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_160)) (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_161 f)) (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_161 f)) (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0159 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0155) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0157 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0163 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0161 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0018 f a))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0163 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0161 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0018 f a))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0027 f a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0159 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0155) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0157 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0163 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0161 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0018 f a))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0163 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0161 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0018 f a))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)), ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)), ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)), ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)), ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0027 f a)))))))))))))))))))

theorem nb057_compact_fv_empty_0128 : (nb057_alpha_dummy_182) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0424 : (nb057_alpha_dummy_182) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_182, fv_syn_c1c] using (nb057_compact_fv_empty_0128)

theorem nb057_compact_fv_empty_0129 (f : Var) : (nb057_alpha_dummy_185 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0425 (f : Var) : (nb057_alpha_dummy_185 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_185, fv_syn_c1c] using (nb057_compact_fv_empty_0129 f)

theorem nb057_compact_fv_empty_0130 : (nb057_alpha_dummy_181) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0426 : (nb057_alpha_dummy_181) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_181, fv_syn_c1c] using (nb057_compact_fv_empty_0130)

theorem nb057_compact_fv_empty_0131 (f : Var) : (nb057_alpha_dummy_184 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0427 (f : Var) : (nb057_alpha_dummy_184 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_184, fv_syn_c1c] using (nb057_compact_fv_empty_0131 f)

theorem nb057_compact_fv_empty_0132 : (nb057_alpha_dummy_180) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0428 : (nb057_alpha_dummy_180) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_180, fv_syn_c1c] using (nb057_compact_fv_empty_0132)

theorem nb057_compact_fv_empty_0133 (f : Var) : (nb057_alpha_dummy_183 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0429 (f : Var) : (nb057_alpha_dummy_183 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_183, fv_syn_c1c] using (nb057_compact_fv_empty_0133 f)

theorem nb057_compact_fv_empty_0134 : (nb057_alpha_dummy_178) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0430 : (nb057_alpha_dummy_178) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_178, fv_syn_c1c] using (nb057_compact_fv_empty_0134)

theorem nb057_compact_fv_empty_0135 (f : Var) : (nb057_alpha_dummy_179 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0431 (f : Var) : (nb057_alpha_dummy_179 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_179, fv_syn_c1c] using (nb057_compact_fv_empty_0135 f)

theorem nb057_compact_fv_empty_0136 : (nb057_alpha_dummy_174) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0432 : (nb057_alpha_dummy_174) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_174, fv_syn_c1c] using (nb057_compact_fv_empty_0136)

theorem nb057_compact_fv_empty_0137 (f : Var) : (nb057_alpha_dummy_176 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0433 (f : Var) : (nb057_alpha_dummy_176 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_176, fv_syn_c1c] using (nb057_compact_fv_empty_0137 f)

theorem nb057_compact_fv_empty_0138 : (nb057_alpha_dummy_175) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0434 : (nb057_alpha_dummy_175) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_175, fv_syn_c1c] using (nb057_compact_fv_empty_0138)

theorem nb057_compact_fv_empty_0139 (f : Var) : (nb057_alpha_dummy_177 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0435 (f : Var) : (nb057_alpha_dummy_177 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_177, fv_syn_c1c] using (nb057_compact_fv_empty_0139 f)

theorem nb057_compact_fv_empty_0140 : (nb057_alpha_dummy_167) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0436 : (nb057_alpha_dummy_167) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_167, fv_syn_c1c] using (nb057_compact_fv_empty_0140)

theorem nb057_compact_fv_empty_0141 (f : Var) : (nb057_alpha_dummy_169 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0437 (f : Var) : (nb057_alpha_dummy_169 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_169, fv_syn_c1c] using (nb057_compact_fv_empty_0141 f)

theorem nb057_compact_fv_empty_0142 : (nb057_alpha_dummy_166) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0438 : (nb057_alpha_dummy_166) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_166, fv_syn_c1c] using (nb057_compact_fv_empty_0142)

theorem nb057_compact_fv_empty_0143 (f : Var) : (nb057_alpha_dummy_168 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0439 (f : Var) : (nb057_alpha_dummy_168 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_168, fv_syn_c1c] using (nb057_compact_fv_empty_0143 f)

theorem nb057_compact_fv_empty_0144 : (nb057_alpha_dummy_172) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0440 : (nb057_alpha_dummy_172) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_172, fv_syn_c1c] using (nb057_compact_fv_empty_0144)

theorem nb057_compact_fv_empty_0145 (f : Var) : (nb057_alpha_dummy_173 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0441 (f : Var) : (nb057_alpha_dummy_173 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_173, fv_syn_c1c] using (nb057_compact_fv_empty_0145 f)

theorem nb057_compact_fv_empty_0146 : (nb057_alpha_dummy_170) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0442 : (nb057_alpha_dummy_170) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_170, fv_syn_c1c] using (nb057_compact_fv_empty_0146)

theorem nb057_compact_fv_empty_0147 (f : Var) : (nb057_alpha_dummy_171 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0443 (f : Var) : (nb057_alpha_dummy_171 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_171, fv_syn_c1c] using (nb057_compact_fv_empty_0147 f)

theorem nb057_compact_envfresh_0028 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)), ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)), ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)), ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)), ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)), ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)), ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)), ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)), ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)), ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_182) (nb057_alpha_dummy_185 f) (nb057_wpp_notmem_0424) (nb057_wpp_notmem_0425 f) (TEnvFresh.consFresh (nb057_alpha_dummy_181) (nb057_alpha_dummy_184 f) (nb057_wpp_notmem_0426) (nb057_wpp_notmem_0427 f) (TEnvFresh.consFresh (nb057_alpha_dummy_180) (nb057_alpha_dummy_183 f) (nb057_wpp_notmem_0428) (nb057_wpp_notmem_0429 f) (TEnvFresh.consFresh (nb057_alpha_dummy_178) (nb057_alpha_dummy_179 f) (nb057_wpp_notmem_0430) (nb057_wpp_notmem_0431 f) (TEnvFresh.consFresh (nb057_alpha_dummy_174) (nb057_alpha_dummy_176 f) (nb057_wpp_notmem_0432) (nb057_wpp_notmem_0433 f) (TEnvFresh.consFresh (nb057_alpha_dummy_175) (nb057_alpha_dummy_177 f) (nb057_wpp_notmem_0434) (nb057_wpp_notmem_0435 f) (TEnvFresh.consFresh (nb057_alpha_dummy_167) (nb057_alpha_dummy_169 f) (nb057_wpp_notmem_0436) (nb057_wpp_notmem_0437 f) (TEnvFresh.consFresh (nb057_alpha_dummy_166) (nb057_alpha_dummy_168 f) (nb057_wpp_notmem_0438) (nb057_wpp_notmem_0439 f) (TEnvFresh.consFresh (nb057_alpha_dummy_172) (nb057_alpha_dummy_173 f) (nb057_wpp_notmem_0440) (nb057_wpp_notmem_0441 f) (TEnvFresh.consFresh (nb057_alpha_dummy_170) (nb057_alpha_dummy_171 f) (nb057_wpp_notmem_0442) (nb057_wpp_notmem_0443 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0338) (nb057_wpp_notmem_0339 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0340) (nb057_wpp_notmem_0341 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0342) (nb057_wpp_notmem_0343 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0248) (nb057_wpp_notmem_0249 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0126) (nb057_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0128) (nb057_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0130) (nb057_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0132) (nb057_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0134) (nb057_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb057_wpp_refl_0028 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)), ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)), ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)), ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)), ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)), ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)), ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)), ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)), ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)), ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0028 f a)

theorem nb057_wpp_notmem_0444 : (nb057_alpha_dummy_182) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_182, fv_syn_c0] using (nb057_compact_fv_empty_0128)

theorem nb057_wpp_notmem_0445 (f : Var) : (nb057_alpha_dummy_185 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_185, fv_syn_c0] using (nb057_compact_fv_empty_0129 f)

theorem nb057_wpp_notmem_0446 : (nb057_alpha_dummy_181) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_181, fv_syn_c0] using (nb057_compact_fv_empty_0130)

theorem nb057_wpp_notmem_0447 (f : Var) : (nb057_alpha_dummy_184 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_184, fv_syn_c0] using (nb057_compact_fv_empty_0131 f)

theorem nb057_wpp_notmem_0448 : (nb057_alpha_dummy_180) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_180, fv_syn_c0] using (nb057_compact_fv_empty_0132)

theorem nb057_wpp_notmem_0449 (f : Var) : (nb057_alpha_dummy_183 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_183, fv_syn_c0] using (nb057_compact_fv_empty_0133 f)

theorem nb057_wpp_notmem_0450 : (nb057_alpha_dummy_178) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_178, fv_syn_c0] using (nb057_compact_fv_empty_0134)

theorem nb057_wpp_notmem_0451 (f : Var) : (nb057_alpha_dummy_179 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_179, fv_syn_c0] using (nb057_compact_fv_empty_0135 f)

theorem nb057_wpp_notmem_0452 : (nb057_alpha_dummy_174) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_174, fv_syn_c0] using (nb057_compact_fv_empty_0136)

theorem nb057_wpp_notmem_0453 (f : Var) : (nb057_alpha_dummy_176 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_176, fv_syn_c0] using (nb057_compact_fv_empty_0137 f)

theorem nb057_wpp_notmem_0454 : (nb057_alpha_dummy_175) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_175, fv_syn_c0] using (nb057_compact_fv_empty_0138)

theorem nb057_wpp_notmem_0455 (f : Var) : (nb057_alpha_dummy_177 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_177, fv_syn_c0] using (nb057_compact_fv_empty_0139 f)

theorem nb057_wpp_notmem_0456 : (nb057_alpha_dummy_167) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_167, fv_syn_c0] using (nb057_compact_fv_empty_0140)

theorem nb057_wpp_notmem_0457 (f : Var) : (nb057_alpha_dummy_169 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_169, fv_syn_c0] using (nb057_compact_fv_empty_0141 f)

theorem nb057_wpp_notmem_0458 : (nb057_alpha_dummy_166) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_166, fv_syn_c0] using (nb057_compact_fv_empty_0142)

theorem nb057_wpp_notmem_0459 (f : Var) : (nb057_alpha_dummy_168 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_168, fv_syn_c0] using (nb057_compact_fv_empty_0143 f)

theorem nb057_wpp_notmem_0460 : (nb057_alpha_dummy_172) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_172, fv_syn_c0] using (nb057_compact_fv_empty_0144)

theorem nb057_wpp_notmem_0461 (f : Var) : (nb057_alpha_dummy_173 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_173, fv_syn_c0] using (nb057_compact_fv_empty_0145 f)

theorem nb057_wpp_notmem_0462 : (nb057_alpha_dummy_170) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_170, fv_syn_c0] using (nb057_compact_fv_empty_0146)

theorem nb057_wpp_notmem_0463 (f : Var) : (nb057_alpha_dummy_171 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_171, fv_syn_c0] using (nb057_compact_fv_empty_0147 f)

theorem nb057_compact_envfresh_0029 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)), ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)), ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)), ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)), ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)), ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)), ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)), ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)), ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)), ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_182) (nb057_alpha_dummy_185 f) (nb057_wpp_notmem_0444) (nb057_wpp_notmem_0445 f) (TEnvFresh.consFresh (nb057_alpha_dummy_181) (nb057_alpha_dummy_184 f) (nb057_wpp_notmem_0446) (nb057_wpp_notmem_0447 f) (TEnvFresh.consFresh (nb057_alpha_dummy_180) (nb057_alpha_dummy_183 f) (nb057_wpp_notmem_0448) (nb057_wpp_notmem_0449 f) (TEnvFresh.consFresh (nb057_alpha_dummy_178) (nb057_alpha_dummy_179 f) (nb057_wpp_notmem_0450) (nb057_wpp_notmem_0451 f) (TEnvFresh.consFresh (nb057_alpha_dummy_174) (nb057_alpha_dummy_176 f) (nb057_wpp_notmem_0452) (nb057_wpp_notmem_0453 f) (TEnvFresh.consFresh (nb057_alpha_dummy_175) (nb057_alpha_dummy_177 f) (nb057_wpp_notmem_0454) (nb057_wpp_notmem_0455 f) (TEnvFresh.consFresh (nb057_alpha_dummy_167) (nb057_alpha_dummy_169 f) (nb057_wpp_notmem_0456) (nb057_wpp_notmem_0457 f) (TEnvFresh.consFresh (nb057_alpha_dummy_166) (nb057_alpha_dummy_168 f) (nb057_wpp_notmem_0458) (nb057_wpp_notmem_0459 f) (TEnvFresh.consFresh (nb057_alpha_dummy_172) (nb057_alpha_dummy_173 f) (nb057_wpp_notmem_0460) (nb057_wpp_notmem_0461 f) (TEnvFresh.consFresh (nb057_alpha_dummy_170) (nb057_alpha_dummy_171 f) (nb057_wpp_notmem_0462) (nb057_wpp_notmem_0463 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0364) (nb057_wpp_notmem_0365 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0366) (nb057_wpp_notmem_0367 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0368) (nb057_wpp_notmem_0369 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0270) (nb057_wpp_notmem_0271 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0156) (nb057_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0158) (nb057_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0160) (nb057_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0162) (nb057_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0164) (nb057_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb057_wpp_refl_0029 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)), ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)), ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)), ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)), ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)), ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)), ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)), ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)), ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)), ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0029 f a)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
