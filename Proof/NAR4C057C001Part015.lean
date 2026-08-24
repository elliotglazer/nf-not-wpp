import NAR4C057C001Part014

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

theorem nb057_wpp_notmem_0505 (f : Var) : (nb057_alpha_dummy_171 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_171, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0147 f)

theorem nb057_compact_envfresh_0034 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)), ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)), ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)), ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)), ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_198) (nb057_alpha_dummy_199 f) (nb057_wpp_notmem_0496) (nb057_wpp_notmem_0497 f) (TEnvFresh.consFresh (nb057_alpha_dummy_167) (nb057_alpha_dummy_169 f) (nb057_wpp_notmem_0498) (nb057_wpp_notmem_0499 f) (TEnvFresh.consFresh (nb057_alpha_dummy_166) (nb057_alpha_dummy_168 f) (nb057_wpp_notmem_0500) (nb057_wpp_notmem_0501 f) (TEnvFresh.consFresh (nb057_alpha_dummy_196) (nb057_alpha_dummy_197 f) (nb057_wpp_notmem_0502) (nb057_wpp_notmem_0503 f) (TEnvFresh.consFresh (nb057_alpha_dummy_170) (nb057_alpha_dummy_171 f) (nb057_wpp_notmem_0504) (nb057_wpp_notmem_0505 f) (TEnvFresh.consFresh (nb057_alpha_dummy_125) (nb057_alpha_dummy_127 f) (nb057_wpp_notmem_0418) (nb057_wpp_notmem_0419 f) (TEnvFresh.consFresh (nb057_alpha_dummy_124) (nb057_alpha_dummy_126 f) (nb057_wpp_notmem_0420) (nb057_wpp_notmem_0421 f) (TEnvFresh.consFresh (nb057_alpha_dummy_128) (nb057_alpha_dummy_129 f) (nb057_wpp_notmem_0422) (nb057_wpp_notmem_0423 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0316) (nb057_wpp_notmem_0317 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0218) (nb057_wpp_notmem_0219 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0220) (nb057_wpp_notmem_0221 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0222) (nb057_wpp_notmem_0223 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0224) (nb057_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0226) (nb057_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0100) (nb057_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0102) (nb057_wpp_notmem_0103 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0104) (nb057_wpp_notmem_0105 f a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))

noncomputable def nb057_wpp_refl_0034 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)), ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)), ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)), ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)), ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0034 f a)

noncomputable def nb057_split_alpha_0024 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)), ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_196)) (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_196)) (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_197 f)) (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_197 f)) (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0197 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0193) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0195 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0201 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0199 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0023 f a))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0201 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0199 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0023 f a))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)), ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)), ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)), ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)), ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0034 f a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0197 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0193) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0195 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0201 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0199 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0023 f a))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0201 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0199 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0023 f a))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)), ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)), ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)), ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)), ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)), ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0034 f a)))))))))))))))))))

noncomputable def nb057_split_alpha_0025 (f : Var) (a : Var) (dv_a_f : a ≠ f) : TAlphaWff [((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)), ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)), ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (Class.cv (nb057_alpha_dummy_128)) (syn_cop (Class.cv (nb057_alpha_dummy_124)) (Class.cv (nb057_alpha_dummy_125)))) (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_124))))) (Wff.imp (Wff.classEq (Class.cv (nb057_alpha_dummy_129 f)) (syn_cop (Class.cv (nb057_alpha_dummy_126 f)) (Class.cv (nb057_alpha_dummy_127 f)))) (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_126 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0124) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0125 f) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0122) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0123 f) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0131 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0127) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0129 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0016 f a))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0131 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0127) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0129 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0016 f a))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0019 f a))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0169 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0165) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0167 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0021 f a))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0169 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0165) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0167 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0021 f a))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0024 f a)))))))))) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0211 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0207) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0209 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0204) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0205 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0203 f) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_a_f) (TAlphaVar.here _ _ _)))))))))))))))

theorem nb057_compact_fv_empty_0154 : (nb057_alpha_dummy_218) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0506 : (nb057_alpha_dummy_218) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_218, fv_syn_c1c] using (nb057_compact_fv_empty_0154)

theorem nb057_compact_fv_empty_0155 (f : Var) : (nb057_alpha_dummy_221 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0507 (f : Var) : (nb057_alpha_dummy_221 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_221, fv_syn_c1c] using (nb057_compact_fv_empty_0155 f)

theorem nb057_compact_fv_empty_0156 : (nb057_alpha_dummy_217) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0508 : (nb057_alpha_dummy_217) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_217, fv_syn_c1c] using (nb057_compact_fv_empty_0156)

theorem nb057_compact_fv_empty_0157 (f : Var) : (nb057_alpha_dummy_220 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0509 (f : Var) : (nb057_alpha_dummy_220 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_220, fv_syn_c1c] using (nb057_compact_fv_empty_0157 f)

theorem nb057_compact_fv_empty_0158 : (nb057_alpha_dummy_216) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0510 : (nb057_alpha_dummy_216) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_216, fv_syn_c1c] using (nb057_compact_fv_empty_0158)

theorem nb057_compact_fv_empty_0159 (f : Var) : (nb057_alpha_dummy_219 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0511 (f : Var) : (nb057_alpha_dummy_219 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_219, fv_syn_c1c] using (nb057_compact_fv_empty_0159 f)

theorem nb057_compact_fv_empty_0160 : (nb057_alpha_dummy_214) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0512 : (nb057_alpha_dummy_214) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_214, fv_syn_c1c] using (nb057_compact_fv_empty_0160)

theorem nb057_compact_fv_empty_0161 (f : Var) : (nb057_alpha_dummy_215 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0513 (f : Var) : (nb057_alpha_dummy_215 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_215, fv_syn_c1c] using (nb057_compact_fv_empty_0161 f)

theorem nb057_compact_fv_empty_0162 : (nb057_alpha_dummy_210) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0514 : (nb057_alpha_dummy_210) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_210, fv_syn_c1c] using (nb057_compact_fv_empty_0162)

theorem nb057_compact_fv_empty_0163 (f : Var) : (nb057_alpha_dummy_212 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0515 (f : Var) : (nb057_alpha_dummy_212 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_212, fv_syn_c1c] using (nb057_compact_fv_empty_0163 f)

theorem nb057_compact_fv_empty_0164 : (nb057_alpha_dummy_211) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0516 : (nb057_alpha_dummy_211) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_211, fv_syn_c1c] using (nb057_compact_fv_empty_0164)

theorem nb057_compact_fv_empty_0165 (f : Var) : (nb057_alpha_dummy_213 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0517 (f : Var) : (nb057_alpha_dummy_213 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_213, fv_syn_c1c] using (nb057_compact_fv_empty_0165 f)

theorem nb057_compact_fv_empty_0166 : (nb057_alpha_dummy_203) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0518 : (nb057_alpha_dummy_203) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_203, fv_syn_c1c] using (nb057_compact_fv_empty_0166)

theorem nb057_compact_fv_empty_0167 (f : Var) : (nb057_alpha_dummy_205 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0519 (f : Var) : (nb057_alpha_dummy_205 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_205, fv_syn_c1c] using (nb057_compact_fv_empty_0167 f)

theorem nb057_compact_fv_empty_0168 : (nb057_alpha_dummy_202) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0520 : (nb057_alpha_dummy_202) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_202, fv_syn_c1c] using (nb057_compact_fv_empty_0168)

theorem nb057_compact_fv_empty_0169 (f : Var) : (nb057_alpha_dummy_204 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0521 (f : Var) : (nb057_alpha_dummy_204 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_204, fv_syn_c1c] using (nb057_compact_fv_empty_0169 f)

theorem nb057_compact_fv_empty_0170 : (nb057_alpha_dummy_208) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0522 : (nb057_alpha_dummy_208) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_208, fv_syn_c1c] using (nb057_compact_fv_empty_0170)

theorem nb057_compact_fv_empty_0171 (f : Var) : (nb057_alpha_dummy_209 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0523 (f : Var) : (nb057_alpha_dummy_209 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_209, fv_syn_c1c] using (nb057_compact_fv_empty_0171 f)

theorem nb057_compact_fv_empty_0172 : (nb057_alpha_dummy_206) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0524 : (nb057_alpha_dummy_206) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_206, fv_syn_c1c] using (nb057_compact_fv_empty_0172)

theorem nb057_compact_fv_empty_0173 (f : Var) : (nb057_alpha_dummy_207 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0525 (f : Var) : (nb057_alpha_dummy_207 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_207, fv_syn_c1c] using (nb057_compact_fv_empty_0173 f)

theorem nb057_compact_envfresh_0035 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)), ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)), ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)), ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_218) (nb057_alpha_dummy_221 f) (nb057_wpp_notmem_0506) (nb057_wpp_notmem_0507 f) (TEnvFresh.consFresh (nb057_alpha_dummy_217) (nb057_alpha_dummy_220 f) (nb057_wpp_notmem_0508) (nb057_wpp_notmem_0509 f) (TEnvFresh.consFresh (nb057_alpha_dummy_216) (nb057_alpha_dummy_219 f) (nb057_wpp_notmem_0510) (nb057_wpp_notmem_0511 f) (TEnvFresh.consFresh (nb057_alpha_dummy_214) (nb057_alpha_dummy_215 f) (nb057_wpp_notmem_0512) (nb057_wpp_notmem_0513 f) (TEnvFresh.consFresh (nb057_alpha_dummy_210) (nb057_alpha_dummy_212 f) (nb057_wpp_notmem_0514) (nb057_wpp_notmem_0515 f) (TEnvFresh.consFresh (nb057_alpha_dummy_211) (nb057_alpha_dummy_213 f) (nb057_wpp_notmem_0516) (nb057_wpp_notmem_0517 f) (TEnvFresh.consFresh (nb057_alpha_dummy_203) (nb057_alpha_dummy_205 f) (nb057_wpp_notmem_0518) (nb057_wpp_notmem_0519 f) (TEnvFresh.consFresh (nb057_alpha_dummy_202) (nb057_alpha_dummy_204 f) (nb057_wpp_notmem_0520) (nb057_wpp_notmem_0521 f) (TEnvFresh.consFresh (nb057_alpha_dummy_208) (nb057_alpha_dummy_209 f) (nb057_wpp_notmem_0522) (nb057_wpp_notmem_0523 f) (TEnvFresh.consFresh (nb057_alpha_dummy_206) (nb057_alpha_dummy_207 f) (nb057_wpp_notmem_0524) (nb057_wpp_notmem_0525 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0248) (nb057_wpp_notmem_0249 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0126) (nb057_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0128) (nb057_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0130) (nb057_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0132) (nb057_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0134) (nb057_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb057_wpp_refl_0035 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)), ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)), ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)), ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0035 f a)

theorem nb057_wpp_notmem_0526 : (nb057_alpha_dummy_218) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_218, fv_syn_c0] using (nb057_compact_fv_empty_0154)

theorem nb057_wpp_notmem_0527 (f : Var) : (nb057_alpha_dummy_221 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_221, fv_syn_c0] using (nb057_compact_fv_empty_0155 f)

theorem nb057_wpp_notmem_0528 : (nb057_alpha_dummy_217) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_217, fv_syn_c0] using (nb057_compact_fv_empty_0156)

theorem nb057_wpp_notmem_0529 (f : Var) : (nb057_alpha_dummy_220 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_220, fv_syn_c0] using (nb057_compact_fv_empty_0157 f)

theorem nb057_wpp_notmem_0530 : (nb057_alpha_dummy_216) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_216, fv_syn_c0] using (nb057_compact_fv_empty_0158)

theorem nb057_wpp_notmem_0531 (f : Var) : (nb057_alpha_dummy_219 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_219, fv_syn_c0] using (nb057_compact_fv_empty_0159 f)

theorem nb057_wpp_notmem_0532 : (nb057_alpha_dummy_214) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_214, fv_syn_c0] using (nb057_compact_fv_empty_0160)

theorem nb057_wpp_notmem_0533 (f : Var) : (nb057_alpha_dummy_215 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_215, fv_syn_c0] using (nb057_compact_fv_empty_0161 f)

theorem nb057_wpp_notmem_0534 : (nb057_alpha_dummy_210) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_210, fv_syn_c0] using (nb057_compact_fv_empty_0162)

theorem nb057_wpp_notmem_0535 (f : Var) : (nb057_alpha_dummy_212 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_212, fv_syn_c0] using (nb057_compact_fv_empty_0163 f)

theorem nb057_wpp_notmem_0536 : (nb057_alpha_dummy_211) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_211, fv_syn_c0] using (nb057_compact_fv_empty_0164)

theorem nb057_wpp_notmem_0537 (f : Var) : (nb057_alpha_dummy_213 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_213, fv_syn_c0] using (nb057_compact_fv_empty_0165 f)

theorem nb057_wpp_notmem_0538 : (nb057_alpha_dummy_203) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_203, fv_syn_c0] using (nb057_compact_fv_empty_0166)

theorem nb057_wpp_notmem_0539 (f : Var) : (nb057_alpha_dummy_205 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_205, fv_syn_c0] using (nb057_compact_fv_empty_0167 f)

theorem nb057_wpp_notmem_0540 : (nb057_alpha_dummy_202) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_202, fv_syn_c0] using (nb057_compact_fv_empty_0168)

theorem nb057_wpp_notmem_0541 (f : Var) : (nb057_alpha_dummy_204 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_204, fv_syn_c0] using (nb057_compact_fv_empty_0169 f)

theorem nb057_wpp_notmem_0542 : (nb057_alpha_dummy_208) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_208, fv_syn_c0] using (nb057_compact_fv_empty_0170)

theorem nb057_wpp_notmem_0543 (f : Var) : (nb057_alpha_dummy_209 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_209, fv_syn_c0] using (nb057_compact_fv_empty_0171 f)

theorem nb057_wpp_notmem_0544 : (nb057_alpha_dummy_206) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_206, fv_syn_c0] using (nb057_compact_fv_empty_0172)

theorem nb057_wpp_notmem_0545 (f : Var) : (nb057_alpha_dummy_207 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_207, fv_syn_c0] using (nb057_compact_fv_empty_0173 f)

theorem nb057_compact_envfresh_0036 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)), ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)), ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)), ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_218) (nb057_alpha_dummy_221 f) (nb057_wpp_notmem_0526) (nb057_wpp_notmem_0527 f) (TEnvFresh.consFresh (nb057_alpha_dummy_217) (nb057_alpha_dummy_220 f) (nb057_wpp_notmem_0528) (nb057_wpp_notmem_0529 f) (TEnvFresh.consFresh (nb057_alpha_dummy_216) (nb057_alpha_dummy_219 f) (nb057_wpp_notmem_0530) (nb057_wpp_notmem_0531 f) (TEnvFresh.consFresh (nb057_alpha_dummy_214) (nb057_alpha_dummy_215 f) (nb057_wpp_notmem_0532) (nb057_wpp_notmem_0533 f) (TEnvFresh.consFresh (nb057_alpha_dummy_210) (nb057_alpha_dummy_212 f) (nb057_wpp_notmem_0534) (nb057_wpp_notmem_0535 f) (TEnvFresh.consFresh (nb057_alpha_dummy_211) (nb057_alpha_dummy_213 f) (nb057_wpp_notmem_0536) (nb057_wpp_notmem_0537 f) (TEnvFresh.consFresh (nb057_alpha_dummy_203) (nb057_alpha_dummy_205 f) (nb057_wpp_notmem_0538) (nb057_wpp_notmem_0539 f) (TEnvFresh.consFresh (nb057_alpha_dummy_202) (nb057_alpha_dummy_204 f) (nb057_wpp_notmem_0540) (nb057_wpp_notmem_0541 f) (TEnvFresh.consFresh (nb057_alpha_dummy_208) (nb057_alpha_dummy_209 f) (nb057_wpp_notmem_0542) (nb057_wpp_notmem_0543 f) (TEnvFresh.consFresh (nb057_alpha_dummy_206) (nb057_alpha_dummy_207 f) (nb057_wpp_notmem_0544) (nb057_wpp_notmem_0545 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0270) (nb057_wpp_notmem_0271 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0156) (nb057_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0158) (nb057_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0160) (nb057_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0162) (nb057_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0164) (nb057_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb057_wpp_refl_0036 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)), ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)), ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)), ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0036 f a)

noncomputable def nb057_split_alpha_0026 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)), ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)), ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)), ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_216)) (syn_cun (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_219 f)) (syn_cun (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0228) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0229 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0226) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0227 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0232) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0233 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0230) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0231 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0228) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0229 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0226) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0227 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0232) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0233 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0230) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0231 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)), ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)), ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)), ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0036 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0236) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0237 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0234) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0235 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0236) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0237 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0234) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0235 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0240) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0241 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0238) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0239 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0240) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0241 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0238) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0239 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0546 : (nb057_alpha_dummy_214) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_214, fv_syn_cnnc] using (nb057_compact_fv_empty_0160)

theorem nb057_wpp_notmem_0547 (f : Var) : (nb057_alpha_dummy_215 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_215, fv_syn_cnnc] using (nb057_compact_fv_empty_0161 f)

theorem nb057_wpp_notmem_0548 : (nb057_alpha_dummy_210) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_210, fv_syn_cnnc] using (nb057_compact_fv_empty_0162)

theorem nb057_wpp_notmem_0549 (f : Var) : (nb057_alpha_dummy_212 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_212, fv_syn_cnnc] using (nb057_compact_fv_empty_0163 f)

theorem nb057_wpp_notmem_0550 : (nb057_alpha_dummy_211) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_211, fv_syn_cnnc] using (nb057_compact_fv_empty_0164)

theorem nb057_wpp_notmem_0551 (f : Var) : (nb057_alpha_dummy_213 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_213, fv_syn_cnnc] using (nb057_compact_fv_empty_0165 f)

theorem nb057_wpp_notmem_0552 : (nb057_alpha_dummy_203) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_203, fv_syn_cnnc] using (nb057_compact_fv_empty_0166)

theorem nb057_wpp_notmem_0553 (f : Var) : (nb057_alpha_dummy_205 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_205, fv_syn_cnnc] using (nb057_compact_fv_empty_0167 f)

theorem nb057_wpp_notmem_0554 : (nb057_alpha_dummy_202) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_202, fv_syn_cnnc] using (nb057_compact_fv_empty_0168)

theorem nb057_wpp_notmem_0555 (f : Var) : (nb057_alpha_dummy_204 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_204, fv_syn_cnnc] using (nb057_compact_fv_empty_0169 f)

theorem nb057_wpp_notmem_0556 : (nb057_alpha_dummy_208) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_208, fv_syn_cnnc] using (nb057_compact_fv_empty_0170)

theorem nb057_wpp_notmem_0557 (f : Var) : (nb057_alpha_dummy_209 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_209, fv_syn_cnnc] using (nb057_compact_fv_empty_0171 f)

theorem nb057_wpp_notmem_0558 : (nb057_alpha_dummy_206) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_206, fv_syn_cnnc] using (nb057_compact_fv_empty_0172)

theorem nb057_wpp_notmem_0559 (f : Var) : (nb057_alpha_dummy_207 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_207, fv_syn_cnnc] using (nb057_compact_fv_empty_0173 f)

theorem nb057_compact_envfresh_0037 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_214) (nb057_alpha_dummy_215 f) (nb057_wpp_notmem_0546) (nb057_wpp_notmem_0547 f) (TEnvFresh.consFresh (nb057_alpha_dummy_210) (nb057_alpha_dummy_212 f) (nb057_wpp_notmem_0548) (nb057_wpp_notmem_0549 f) (TEnvFresh.consFresh (nb057_alpha_dummy_211) (nb057_alpha_dummy_213 f) (nb057_wpp_notmem_0550) (nb057_wpp_notmem_0551 f) (TEnvFresh.consFresh (nb057_alpha_dummy_203) (nb057_alpha_dummy_205 f) (nb057_wpp_notmem_0552) (nb057_wpp_notmem_0553 f) (TEnvFresh.consFresh (nb057_alpha_dummy_202) (nb057_alpha_dummy_204 f) (nb057_wpp_notmem_0554) (nb057_wpp_notmem_0555 f) (TEnvFresh.consFresh (nb057_alpha_dummy_208) (nb057_alpha_dummy_209 f) (nb057_wpp_notmem_0556) (nb057_wpp_notmem_0557 f) (TEnvFresh.consFresh (nb057_alpha_dummy_206) (nb057_alpha_dummy_207 f) (nb057_wpp_notmem_0558) (nb057_wpp_notmem_0559 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0286) (nb057_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0180) (nb057_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0182) (nb057_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0184) (nb057_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0186) (nb057_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0188) (nb057_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb057_wpp_refl_0037 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0037 f a)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
