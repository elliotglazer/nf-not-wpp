import NAR4C057C001Part022

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

theorem nb057_compact_envfresh_0076 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)), ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_214) (nb057_alpha_dummy_215 f) (nb057_wpp_notmem_0546) (nb057_wpp_notmem_0547 f) (TEnvFresh.consFresh (nb057_alpha_dummy_210) (nb057_alpha_dummy_212 f) (nb057_wpp_notmem_0548) (nb057_wpp_notmem_0549 f) (TEnvFresh.consFresh (nb057_alpha_dummy_211) (nb057_alpha_dummy_213 f) (nb057_wpp_notmem_0550) (nb057_wpp_notmem_0551 f) (TEnvFresh.consFresh (nb057_alpha_dummy_236) (nb057_alpha_dummy_237 f) (nb057_wpp_notmem_0572) (nb057_wpp_notmem_0573 f) (TEnvFresh.consFresh (nb057_alpha_dummy_234) (nb057_alpha_dummy_235 f) (nb057_wpp_notmem_0574) (nb057_wpp_notmem_0575 f) (TEnvFresh.consFresh (nb057_alpha_dummy_203) (nb057_alpha_dummy_205 f) (nb057_wpp_notmem_0552) (nb057_wpp_notmem_0553 f) (TEnvFresh.consFresh (nb057_alpha_dummy_202) (nb057_alpha_dummy_204 f) (nb057_wpp_notmem_0554) (nb057_wpp_notmem_0555 f) (TEnvFresh.consFresh (nb057_alpha_dummy_232) (nb057_alpha_dummy_233 f) (nb057_wpp_notmem_0576) (nb057_wpp_notmem_0577 f) (TEnvFresh.consFresh (nb057_alpha_dummy_206) (nb057_alpha_dummy_207 f) (nb057_wpp_notmem_0558) (nb057_wpp_notmem_0559 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0286) (nb057_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0180) (nb057_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0182) (nb057_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0184) (nb057_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb057_wpp_refl_0076 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)), ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0076 f a)

noncomputable def nb057_split_alpha_0057 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)), ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (Class.cv (nb057_alpha_dummy_203))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_211)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_210)))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (Class.cv (nb057_alpha_dummy_205 f))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_213 f)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_212 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0220) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0221 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0220) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0221 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0250) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0251 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0248) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0249 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_203))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_205 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0224) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0225 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0224) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0225 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)), ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)), ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)), ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)), ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0074 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0056 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)), ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0076 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)), ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)), ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)), ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)), ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0076 f a))))))))))))

theorem nb057_compact_envfresh_0077 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_234) (nb057_alpha_dummy_235 f) (nb057_wpp_notmem_0578) (nb057_wpp_notmem_0579 f) (TEnvFresh.consFresh (nb057_alpha_dummy_203) (nb057_alpha_dummy_205 f) (nb057_wpp_notmem_0580) (nb057_wpp_notmem_0581 f) (TEnvFresh.consFresh (nb057_alpha_dummy_202) (nb057_alpha_dummy_204 f) (nb057_wpp_notmem_0582) (nb057_wpp_notmem_0583 f) (TEnvFresh.consFresh (nb057_alpha_dummy_232) (nb057_alpha_dummy_233 f) (nb057_wpp_notmem_0584) (nb057_wpp_notmem_0585 f) (TEnvFresh.consFresh (nb057_alpha_dummy_206) (nb057_alpha_dummy_207 f) (nb057_wpp_notmem_0586) (nb057_wpp_notmem_0587 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0316) (nb057_wpp_notmem_0317 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0218) (nb057_wpp_notmem_0219 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0220) (nb057_wpp_notmem_0221 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0222) (nb057_wpp_notmem_0223 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0100) (nb057_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0102) (nb057_wpp_notmem_0103 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0104) (nb057_wpp_notmem_0105 f a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))

noncomputable def nb057_wpp_refl_0077 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0077 f a)

noncomputable def nb057_split_alpha_0058 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_232)) (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_232)) (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_233 f)) (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_233 f)) (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0246) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0247 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0243) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0245 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0057 f a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0057 f a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0077 f a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0246) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0247 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0243) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0245 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0057 f a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0057 f a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)), ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)), ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)), ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)), ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0077 f a)))))))))))))))))))

noncomputable def nb057_split_alpha_0059 (f : Var) (a : Var) (dv_a_f : a ≠ f) : TAlphaWff [((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (syn_wbr (Class.cv (nb057_alpha_dummy_044)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046))) (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045))))) (Wff.imp (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb057_alpha_dummy_049 f))) (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_048 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0089 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0085) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (nb057_split_alpha_0039 f a))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0089 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0085) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (nb057_split_alpha_0039 f a))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0042 f a)))))))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0053 f a dv_a_f)))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0218) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0219 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0215) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0217 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0055 f a))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0218) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0219 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0215) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0217 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb057_split_alpha_0055 f a))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0058 f a)))))))))) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0207) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0209 f) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_a_f) (TAlphaVar.here _ _ _))))))))))

theorem nb057_compact_fv_empty_0180 : (nb057_alpha_dummy_239) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0598 : (nb057_alpha_dummy_239) ∉ ((syn_cvv)).fv := by
  simpa only [nb057_alpha_dummy_239, fv_syn_cvv] using (nb057_compact_fv_empty_0180)

theorem nb057_compact_fv_empty_0181 (f : Var) : (nb057_alpha_dummy_241 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0599 (f : Var) : (nb057_alpha_dummy_241 f) ∉ ((syn_cvv)).fv := by
  simpa only [nb057_alpha_dummy_241, fv_syn_cvv] using (nb057_compact_fv_empty_0181 f)

theorem nb057_compact_fv_empty_0182 : (nb057_alpha_dummy_238) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0600 : (nb057_alpha_dummy_238) ∉ ((syn_cvv)).fv := by
  simpa only [nb057_alpha_dummy_238, fv_syn_cvv] using (nb057_compact_fv_empty_0182)

theorem nb057_compact_fv_empty_0183 (f : Var) : (nb057_alpha_dummy_240 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0601 (f : Var) : (nb057_alpha_dummy_240 f) ∉ ((syn_cvv)).fv := by
  simpa only [nb057_alpha_dummy_240, fv_syn_cvv] using (nb057_compact_fv_empty_0183 f)

theorem nb057_wpp_notmem_0602 : (nb057_alpha_dummy_000) ∉ ((syn_cvv)).fv := by
  simpa only [nb057_alpha_dummy_000, fv_syn_cvv] using (nb057_compact_fv_empty_0020)

theorem nb057_wpp_notmem_0603 (a : Var) : a ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb057_compact_fv_empty_0021 a)

theorem nb057_wpp_notmem_0604 : (nb057_alpha_dummy_001) ∉ ((syn_cvv)).fv := by
  simpa only [nb057_alpha_dummy_001, fv_syn_cvv] using (nb057_compact_fv_empty_0022)

theorem nb057_wpp_notmem_0605 (f : Var) : f ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb057_compact_fv_empty_0023 f)

theorem nb057_wpp_notmem_0606 : (nb057_alpha_dummy_002) ∉ ((syn_cvv)).fv := by
  simpa only [nb057_alpha_dummy_002, fv_syn_cvv] using (nb057_compact_fv_empty_0024)

theorem nb057_wpp_notmem_0607 (f : Var) (a : Var) : (nb057_alpha_dummy_003 f a) ∉ ((syn_cvv)).fv := by
  simpa only [nb057_alpha_dummy_003, fv_syn_cvv] using (nb057_compact_fv_empty_0025 f a)

theorem nb057_compact_envfresh_0078 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)), ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_239) (nb057_alpha_dummy_241 f) (nb057_wpp_notmem_0598) (nb057_wpp_notmem_0599 f) (TEnvFresh.consFresh (nb057_alpha_dummy_238) (nb057_alpha_dummy_240 f) (nb057_wpp_notmem_0600) (nb057_wpp_notmem_0601 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0602) (nb057_wpp_notmem_0603 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0604) (nb057_wpp_notmem_0605 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0606) (nb057_wpp_notmem_0607 f a) (TEnvFresh.nil ((syn_cvv)).fv))))))

noncomputable def nb057_wpp_refl_0078 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)), ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0078 f a)

theorem nb057_compact_fv_empty_0184 : (nb057_alpha_dummy_258) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0608 : (nb057_alpha_dummy_258) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_258, fv_syn_c1c] using (nb057_compact_fv_empty_0184)

theorem nb057_compact_fv_empty_0185 (f : Var) : (nb057_alpha_dummy_261 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0609 (f : Var) : (nb057_alpha_dummy_261 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_261, fv_syn_c1c] using (nb057_compact_fv_empty_0185 f)

theorem nb057_compact_fv_empty_0186 : (nb057_alpha_dummy_257) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0610 : (nb057_alpha_dummy_257) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_257, fv_syn_c1c] using (nb057_compact_fv_empty_0186)

theorem nb057_compact_fv_empty_0187 (f : Var) : (nb057_alpha_dummy_260 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0611 (f : Var) : (nb057_alpha_dummy_260 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_260, fv_syn_c1c] using (nb057_compact_fv_empty_0187 f)

theorem nb057_compact_fv_empty_0188 : (nb057_alpha_dummy_256) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0612 : (nb057_alpha_dummy_256) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_256, fv_syn_c1c] using (nb057_compact_fv_empty_0188)

theorem nb057_compact_fv_empty_0189 (f : Var) : (nb057_alpha_dummy_259 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0613 (f : Var) : (nb057_alpha_dummy_259 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_259, fv_syn_c1c] using (nb057_compact_fv_empty_0189 f)

theorem nb057_compact_fv_empty_0190 : (nb057_alpha_dummy_254) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0614 : (nb057_alpha_dummy_254) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_254, fv_syn_c1c] using (nb057_compact_fv_empty_0190)

theorem nb057_compact_fv_empty_0191 (f : Var) : (nb057_alpha_dummy_255 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0615 (f : Var) : (nb057_alpha_dummy_255 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_255, fv_syn_c1c] using (nb057_compact_fv_empty_0191 f)

theorem nb057_compact_fv_empty_0192 : (nb057_alpha_dummy_250) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0616 : (nb057_alpha_dummy_250) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_250, fv_syn_c1c] using (nb057_compact_fv_empty_0192)

theorem nb057_compact_fv_empty_0193 (f : Var) : (nb057_alpha_dummy_252 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0617 (f : Var) : (nb057_alpha_dummy_252 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_252, fv_syn_c1c] using (nb057_compact_fv_empty_0193 f)

theorem nb057_compact_fv_empty_0194 : (nb057_alpha_dummy_251) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0618 : (nb057_alpha_dummy_251) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_251, fv_syn_c1c] using (nb057_compact_fv_empty_0194)

theorem nb057_compact_fv_empty_0195 (f : Var) : (nb057_alpha_dummy_253 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0619 (f : Var) : (nb057_alpha_dummy_253 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_253, fv_syn_c1c] using (nb057_compact_fv_empty_0195 f)

theorem nb057_compact_fv_empty_0196 : (nb057_alpha_dummy_243) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0620 : (nb057_alpha_dummy_243) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_243, fv_syn_c1c] using (nb057_compact_fv_empty_0196)

theorem nb057_compact_fv_empty_0197 (f : Var) : (nb057_alpha_dummy_245 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0621 (f : Var) : (nb057_alpha_dummy_245 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_245, fv_syn_c1c] using (nb057_compact_fv_empty_0197 f)

theorem nb057_compact_fv_empty_0198 : (nb057_alpha_dummy_242) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0622 : (nb057_alpha_dummy_242) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_242, fv_syn_c1c] using (nb057_compact_fv_empty_0198)

theorem nb057_compact_fv_empty_0199 (f : Var) : (nb057_alpha_dummy_244 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0623 (f : Var) : (nb057_alpha_dummy_244 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_244, fv_syn_c1c] using (nb057_compact_fv_empty_0199 f)

theorem nb057_compact_fv_empty_0200 : (nb057_alpha_dummy_248) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0624 : (nb057_alpha_dummy_248) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_248, fv_syn_c1c] using (nb057_compact_fv_empty_0200)

theorem nb057_compact_fv_empty_0201 (f : Var) : (nb057_alpha_dummy_249 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0625 (f : Var) : (nb057_alpha_dummy_249 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_249, fv_syn_c1c] using (nb057_compact_fv_empty_0201 f)

theorem nb057_compact_fv_empty_0202 : (nb057_alpha_dummy_246) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0626 : (nb057_alpha_dummy_246) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_246, fv_syn_c1c] using (nb057_compact_fv_empty_0202)

theorem nb057_compact_fv_empty_0203 (f : Var) : (nb057_alpha_dummy_247 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0627 (f : Var) : (nb057_alpha_dummy_247 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_247, fv_syn_c1c] using (nb057_compact_fv_empty_0203 f)

theorem nb057_wpp_notmem_0628 : (nb057_alpha_dummy_239) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_239, fv_syn_c1c] using (nb057_compact_fv_empty_0180)

theorem nb057_wpp_notmem_0629 (f : Var) : (nb057_alpha_dummy_241 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_241, fv_syn_c1c] using (nb057_compact_fv_empty_0181 f)

theorem nb057_wpp_notmem_0630 : (nb057_alpha_dummy_238) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_238, fv_syn_c1c] using (nb057_compact_fv_empty_0182)

theorem nb057_wpp_notmem_0631 (f : Var) : (nb057_alpha_dummy_240 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_240, fv_syn_c1c] using (nb057_compact_fv_empty_0183 f)

theorem nb057_compact_envfresh_0079 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)), ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)), ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)), ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)), ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)), ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)), ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)), ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)), ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)), ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)), ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)), ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_258) (nb057_alpha_dummy_261 f) (nb057_wpp_notmem_0608) (nb057_wpp_notmem_0609 f) (TEnvFresh.consFresh (nb057_alpha_dummy_257) (nb057_alpha_dummy_260 f) (nb057_wpp_notmem_0610) (nb057_wpp_notmem_0611 f) (TEnvFresh.consFresh (nb057_alpha_dummy_256) (nb057_alpha_dummy_259 f) (nb057_wpp_notmem_0612) (nb057_wpp_notmem_0613 f) (TEnvFresh.consFresh (nb057_alpha_dummy_254) (nb057_alpha_dummy_255 f) (nb057_wpp_notmem_0614) (nb057_wpp_notmem_0615 f) (TEnvFresh.consFresh (nb057_alpha_dummy_250) (nb057_alpha_dummy_252 f) (nb057_wpp_notmem_0616) (nb057_wpp_notmem_0617 f) (TEnvFresh.consFresh (nb057_alpha_dummy_251) (nb057_alpha_dummy_253 f) (nb057_wpp_notmem_0618) (nb057_wpp_notmem_0619 f) (TEnvFresh.consFresh (nb057_alpha_dummy_243) (nb057_alpha_dummy_245 f) (nb057_wpp_notmem_0620) (nb057_wpp_notmem_0621 f) (TEnvFresh.consFresh (nb057_alpha_dummy_242) (nb057_alpha_dummy_244 f) (nb057_wpp_notmem_0622) (nb057_wpp_notmem_0623 f) (TEnvFresh.consFresh (nb057_alpha_dummy_248) (nb057_alpha_dummy_249 f) (nb057_wpp_notmem_0624) (nb057_wpp_notmem_0625 f) (TEnvFresh.consFresh (nb057_alpha_dummy_246) (nb057_alpha_dummy_247 f) (nb057_wpp_notmem_0626) (nb057_wpp_notmem_0627 f) (TEnvFresh.consFresh (nb057_alpha_dummy_239) (nb057_alpha_dummy_241 f) (nb057_wpp_notmem_0628) (nb057_wpp_notmem_0629 f) (TEnvFresh.consFresh (nb057_alpha_dummy_238) (nb057_alpha_dummy_240 f) (nb057_wpp_notmem_0630) (nb057_wpp_notmem_0631 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb057_wpp_refl_0079 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)), ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)), ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)), ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)), ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)), ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)), ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)), ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)), ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)), ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)), ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)), ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0079 f a)

theorem nb057_wpp_notmem_0632 : (nb057_alpha_dummy_258) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_258, fv_syn_c0] using (nb057_compact_fv_empty_0184)

theorem nb057_wpp_notmem_0633 (f : Var) : (nb057_alpha_dummy_261 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_261, fv_syn_c0] using (nb057_compact_fv_empty_0185 f)

theorem nb057_wpp_notmem_0634 : (nb057_alpha_dummy_257) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_257, fv_syn_c0] using (nb057_compact_fv_empty_0186)

theorem nb057_wpp_notmem_0635 (f : Var) : (nb057_alpha_dummy_260 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_260, fv_syn_c0] using (nb057_compact_fv_empty_0187 f)

theorem nb057_wpp_notmem_0636 : (nb057_alpha_dummy_256) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_256, fv_syn_c0] using (nb057_compact_fv_empty_0188)

theorem nb057_wpp_notmem_0637 (f : Var) : (nb057_alpha_dummy_259 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_259, fv_syn_c0] using (nb057_compact_fv_empty_0189 f)

theorem nb057_wpp_notmem_0638 : (nb057_alpha_dummy_254) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_254, fv_syn_c0] using (nb057_compact_fv_empty_0190)

theorem nb057_wpp_notmem_0639 (f : Var) : (nb057_alpha_dummy_255 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_255, fv_syn_c0] using (nb057_compact_fv_empty_0191 f)

theorem nb057_wpp_notmem_0640 : (nb057_alpha_dummy_250) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_250, fv_syn_c0] using (nb057_compact_fv_empty_0192)

theorem nb057_wpp_notmem_0641 (f : Var) : (nb057_alpha_dummy_252 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_252, fv_syn_c0] using (nb057_compact_fv_empty_0193 f)

theorem nb057_wpp_notmem_0642 : (nb057_alpha_dummy_251) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_251, fv_syn_c0] using (nb057_compact_fv_empty_0194)

theorem nb057_wpp_notmem_0643 (f : Var) : (nb057_alpha_dummy_253 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_253, fv_syn_c0] using (nb057_compact_fv_empty_0195 f)

theorem nb057_wpp_notmem_0644 : (nb057_alpha_dummy_243) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_243, fv_syn_c0] using (nb057_compact_fv_empty_0196)

theorem nb057_wpp_notmem_0645 (f : Var) : (nb057_alpha_dummy_245 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_245, fv_syn_c0] using (nb057_compact_fv_empty_0197 f)

theorem nb057_wpp_notmem_0646 : (nb057_alpha_dummy_242) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_242, fv_syn_c0] using (nb057_compact_fv_empty_0198)

theorem nb057_wpp_notmem_0647 (f : Var) : (nb057_alpha_dummy_244 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_244, fv_syn_c0] using (nb057_compact_fv_empty_0199 f)

theorem nb057_wpp_notmem_0648 : (nb057_alpha_dummy_248) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_248, fv_syn_c0] using (nb057_compact_fv_empty_0200)

theorem nb057_wpp_notmem_0649 (f : Var) : (nb057_alpha_dummy_249 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_249, fv_syn_c0] using (nb057_compact_fv_empty_0201 f)

theorem nb057_wpp_notmem_0650 : (nb057_alpha_dummy_246) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_246, fv_syn_c0] using (nb057_compact_fv_empty_0202)

theorem nb057_wpp_notmem_0651 (f : Var) : (nb057_alpha_dummy_247 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_247, fv_syn_c0] using (nb057_compact_fv_empty_0203 f)

theorem nb057_wpp_notmem_0652 : (nb057_alpha_dummy_239) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_239, fv_syn_c0] using (nb057_compact_fv_empty_0180)

theorem nb057_wpp_notmem_0653 (f : Var) : (nb057_alpha_dummy_241 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_241, fv_syn_c0] using (nb057_compact_fv_empty_0181 f)

theorem nb057_wpp_notmem_0654 : (nb057_alpha_dummy_238) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_238, fv_syn_c0] using (nb057_compact_fv_empty_0182)

theorem nb057_wpp_notmem_0655 (f : Var) : (nb057_alpha_dummy_240 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_240, fv_syn_c0] using (nb057_compact_fv_empty_0183 f)

theorem nb057_compact_envfresh_0080 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)), ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)), ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)), ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)), ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)), ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)), ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)), ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)), ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)), ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)), ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)), ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_258) (nb057_alpha_dummy_261 f) (nb057_wpp_notmem_0632) (nb057_wpp_notmem_0633 f) (TEnvFresh.consFresh (nb057_alpha_dummy_257) (nb057_alpha_dummy_260 f) (nb057_wpp_notmem_0634) (nb057_wpp_notmem_0635 f) (TEnvFresh.consFresh (nb057_alpha_dummy_256) (nb057_alpha_dummy_259 f) (nb057_wpp_notmem_0636) (nb057_wpp_notmem_0637 f) (TEnvFresh.consFresh (nb057_alpha_dummy_254) (nb057_alpha_dummy_255 f) (nb057_wpp_notmem_0638) (nb057_wpp_notmem_0639 f) (TEnvFresh.consFresh (nb057_alpha_dummy_250) (nb057_alpha_dummy_252 f) (nb057_wpp_notmem_0640) (nb057_wpp_notmem_0641 f) (TEnvFresh.consFresh (nb057_alpha_dummy_251) (nb057_alpha_dummy_253 f) (nb057_wpp_notmem_0642) (nb057_wpp_notmem_0643 f) (TEnvFresh.consFresh (nb057_alpha_dummy_243) (nb057_alpha_dummy_245 f) (nb057_wpp_notmem_0644) (nb057_wpp_notmem_0645 f) (TEnvFresh.consFresh (nb057_alpha_dummy_242) (nb057_alpha_dummy_244 f) (nb057_wpp_notmem_0646) (nb057_wpp_notmem_0647 f) (TEnvFresh.consFresh (nb057_alpha_dummy_248) (nb057_alpha_dummy_249 f) (nb057_wpp_notmem_0648) (nb057_wpp_notmem_0649 f) (TEnvFresh.consFresh (nb057_alpha_dummy_246) (nb057_alpha_dummy_247 f) (nb057_wpp_notmem_0650) (nb057_wpp_notmem_0651 f) (TEnvFresh.consFresh (nb057_alpha_dummy_239) (nb057_alpha_dummy_241 f) (nb057_wpp_notmem_0652) (nb057_wpp_notmem_0653 f) (TEnvFresh.consFresh (nb057_alpha_dummy_238) (nb057_alpha_dummy_240 f) (nb057_wpp_notmem_0654) (nb057_wpp_notmem_0655 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb057_wpp_refl_0080 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)), ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)), ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)), ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)), ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)), ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)), ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)), ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)), ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)), ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)), ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)), ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0080 f a)

noncomputable def nb057_split_alpha_0060 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)), ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)), ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)), ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)), ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)), ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)), ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)), ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)), ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)), ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)), ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)), ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_256)) (syn_cun (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_259 f)) (syn_cun (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0266) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0267 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0264) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0265 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0270) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0271 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0268) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0269 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0266) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0267 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0264) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0265 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0270) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0271 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0268) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0269 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)), ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)), ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)), ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)), ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)), ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)), ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)), ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)), ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)), ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)), ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)), ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0080 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0274) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0275 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0272) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0273 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0274) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0275 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0272) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0273 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0278) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0279 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0277 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0278) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0279 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0277 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0656 : (nb057_alpha_dummy_254) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_254, fv_syn_cnnc] using (nb057_compact_fv_empty_0190)

theorem nb057_wpp_notmem_0657 (f : Var) : (nb057_alpha_dummy_255 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_255, fv_syn_cnnc] using (nb057_compact_fv_empty_0191 f)

theorem nb057_wpp_notmem_0658 : (nb057_alpha_dummy_250) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_250, fv_syn_cnnc] using (nb057_compact_fv_empty_0192)

theorem nb057_wpp_notmem_0659 (f : Var) : (nb057_alpha_dummy_252 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_252, fv_syn_cnnc] using (nb057_compact_fv_empty_0193 f)

theorem nb057_wpp_notmem_0660 : (nb057_alpha_dummy_251) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_251, fv_syn_cnnc] using (nb057_compact_fv_empty_0194)

theorem nb057_wpp_notmem_0661 (f : Var) : (nb057_alpha_dummy_253 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_253, fv_syn_cnnc] using (nb057_compact_fv_empty_0195 f)

theorem nb057_wpp_notmem_0662 : (nb057_alpha_dummy_243) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_243, fv_syn_cnnc] using (nb057_compact_fv_empty_0196)

theorem nb057_wpp_notmem_0663 (f : Var) : (nb057_alpha_dummy_245 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_245, fv_syn_cnnc] using (nb057_compact_fv_empty_0197 f)

theorem nb057_wpp_notmem_0664 : (nb057_alpha_dummy_242) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_242, fv_syn_cnnc] using (nb057_compact_fv_empty_0198)

theorem nb057_wpp_notmem_0665 (f : Var) : (nb057_alpha_dummy_244 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_244, fv_syn_cnnc] using (nb057_compact_fv_empty_0199 f)

theorem nb057_wpp_notmem_0666 : (nb057_alpha_dummy_248) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_248, fv_syn_cnnc] using (nb057_compact_fv_empty_0200)

theorem nb057_wpp_notmem_0667 (f : Var) : (nb057_alpha_dummy_249 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_249, fv_syn_cnnc] using (nb057_compact_fv_empty_0201 f)

theorem nb057_wpp_notmem_0668 : (nb057_alpha_dummy_246) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_246, fv_syn_cnnc] using (nb057_compact_fv_empty_0202)

theorem nb057_wpp_notmem_0669 (f : Var) : (nb057_alpha_dummy_247 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_247, fv_syn_cnnc] using (nb057_compact_fv_empty_0203 f)

theorem nb057_wpp_notmem_0670 : (nb057_alpha_dummy_239) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_239, fv_syn_cnnc] using (nb057_compact_fv_empty_0180)

theorem nb057_wpp_notmem_0671 (f : Var) : (nb057_alpha_dummy_241 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_241, fv_syn_cnnc] using (nb057_compact_fv_empty_0181 f)

theorem nb057_wpp_notmem_0672 : (nb057_alpha_dummy_238) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_238, fv_syn_cnnc] using (nb057_compact_fv_empty_0182)

theorem nb057_wpp_notmem_0673 (f : Var) : (nb057_alpha_dummy_240 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_240, fv_syn_cnnc] using (nb057_compact_fv_empty_0183 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
