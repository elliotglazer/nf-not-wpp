import NAR4C078C001Part050

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

noncomputable def nb078_split_alpha_0020 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_199)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_199)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_200 f)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_200 f)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0178) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0179 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0178) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0179 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0208) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0209 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0206) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0207 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_168))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_170 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182), (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)), ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0067 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0187 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0185 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0189 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0187 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0185 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0189 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182), (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)), ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0068 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0193 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0193 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0197 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0197 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0069 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0069 x y f)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0178) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0179 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0178) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0179 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0208) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0209 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0206) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0207 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_168))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_170 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182), (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)), ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0067 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0187 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0185 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0189 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0187 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0185 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0189 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182), (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)), ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0068 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0193 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0193 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0197 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0197 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0069 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0069 x y f)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (nb078_wpp_refl_0070 x y f)))))))

theorem nb078_compact_fv_empty_0154 : (nb078_alpha_dummy_204) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0516 : (nb078_alpha_dummy_204) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_204, fv_syn_cvv] using (nb078_compact_fv_empty_0154)

theorem nb078_compact_fv_empty_0155 (f : Var) : (nb078_alpha_dummy_206 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0517 (f : Var) : (nb078_alpha_dummy_206 f) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_206, fv_syn_cvv] using (nb078_compact_fv_empty_0155 f)

theorem nb078_compact_fv_empty_0156 : (nb078_alpha_dummy_203) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0518 : (nb078_alpha_dummy_203) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_203, fv_syn_cvv] using (nb078_compact_fv_empty_0156)

theorem nb078_compact_fv_empty_0157 (f : Var) : (nb078_alpha_dummy_205 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0519 (f : Var) : (nb078_alpha_dummy_205 f) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_205, fv_syn_cvv] using (nb078_compact_fv_empty_0157 f)

theorem nb078_wpp_notmem_0520 : (nb078_alpha_dummy_000) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_000, fv_syn_cvv] using (nb078_compact_fv_empty_0030)

theorem nb078_wpp_notmem_0521 (f : Var) : f ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb078_compact_fv_empty_0031 f)

theorem nb078_wpp_notmem_0522 : (nb078_alpha_dummy_004) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_004, fv_syn_cvv] using (nb078_compact_fv_empty_0032)

theorem nb078_wpp_notmem_0523 (y : Var) : y ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb078_compact_fv_empty_0033 y)

theorem nb078_wpp_notmem_0524 : (nb078_alpha_dummy_003) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_003, fv_syn_cvv] using (nb078_compact_fv_empty_0034)

theorem nb078_wpp_notmem_0525 (x : Var) : x ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb078_compact_fv_empty_0035 x)

theorem nb078_compact_envfresh_0071 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_204) (nb078_alpha_dummy_206 f) (nb078_wpp_notmem_0516) (nb078_wpp_notmem_0517 f) (TEnvFresh.consFresh (nb078_alpha_dummy_203) (nb078_alpha_dummy_205 f) (nb078_wpp_notmem_0518) (nb078_wpp_notmem_0519 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0520) (nb078_wpp_notmem_0521 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0522) (nb078_wpp_notmem_0523 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0524) (nb078_wpp_notmem_0525 x) (TEnvFresh.nil ((syn_cvv)).fv))))))

noncomputable def nb078_wpp_refl_0071 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0071 x y f)

theorem nb078_compact_fv_empty_0158 : (nb078_alpha_dummy_223) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0526 : (nb078_alpha_dummy_223) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_223, fv_syn_c1c] using (nb078_compact_fv_empty_0158)

theorem nb078_compact_fv_empty_0159 (f : Var) : (nb078_alpha_dummy_226 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0527 (f : Var) : (nb078_alpha_dummy_226 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_226, fv_syn_c1c] using (nb078_compact_fv_empty_0159 f)

theorem nb078_compact_fv_empty_0160 : (nb078_alpha_dummy_222) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0528 : (nb078_alpha_dummy_222) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_222, fv_syn_c1c] using (nb078_compact_fv_empty_0160)

theorem nb078_compact_fv_empty_0161 (f : Var) : (nb078_alpha_dummy_225 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0529 (f : Var) : (nb078_alpha_dummy_225 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_225, fv_syn_c1c] using (nb078_compact_fv_empty_0161 f)

theorem nb078_compact_fv_empty_0162 : (nb078_alpha_dummy_221) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0530 : (nb078_alpha_dummy_221) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_221, fv_syn_c1c] using (nb078_compact_fv_empty_0162)

theorem nb078_compact_fv_empty_0163 (f : Var) : (nb078_alpha_dummy_224 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0531 (f : Var) : (nb078_alpha_dummy_224 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_224, fv_syn_c1c] using (nb078_compact_fv_empty_0163 f)

theorem nb078_compact_fv_empty_0164 : (nb078_alpha_dummy_219) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0532 : (nb078_alpha_dummy_219) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_219, fv_syn_c1c] using (nb078_compact_fv_empty_0164)

theorem nb078_compact_fv_empty_0165 (f : Var) : (nb078_alpha_dummy_220 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0533 (f : Var) : (nb078_alpha_dummy_220 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_220, fv_syn_c1c] using (nb078_compact_fv_empty_0165 f)

theorem nb078_compact_fv_empty_0166 : (nb078_alpha_dummy_215) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0534 : (nb078_alpha_dummy_215) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_215, fv_syn_c1c] using (nb078_compact_fv_empty_0166)

theorem nb078_compact_fv_empty_0167 (f : Var) : (nb078_alpha_dummy_217 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0535 (f : Var) : (nb078_alpha_dummy_217 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_217, fv_syn_c1c] using (nb078_compact_fv_empty_0167 f)

theorem nb078_compact_fv_empty_0168 : (nb078_alpha_dummy_216) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0536 : (nb078_alpha_dummy_216) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_216, fv_syn_c1c] using (nb078_compact_fv_empty_0168)

theorem nb078_compact_fv_empty_0169 (f : Var) : (nb078_alpha_dummy_218 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0537 (f : Var) : (nb078_alpha_dummy_218 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_218, fv_syn_c1c] using (nb078_compact_fv_empty_0169 f)

theorem nb078_compact_fv_empty_0170 : (nb078_alpha_dummy_208) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0538 : (nb078_alpha_dummy_208) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_208, fv_syn_c1c] using (nb078_compact_fv_empty_0170)

theorem nb078_compact_fv_empty_0171 (f : Var) : (nb078_alpha_dummy_210 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0539 (f : Var) : (nb078_alpha_dummy_210 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_210, fv_syn_c1c] using (nb078_compact_fv_empty_0171 f)

theorem nb078_compact_fv_empty_0172 : (nb078_alpha_dummy_207) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0540 : (nb078_alpha_dummy_207) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_207, fv_syn_c1c] using (nb078_compact_fv_empty_0172)

theorem nb078_compact_fv_empty_0173 (f : Var) : (nb078_alpha_dummy_209 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0541 (f : Var) : (nb078_alpha_dummy_209 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_209, fv_syn_c1c] using (nb078_compact_fv_empty_0173 f)

theorem nb078_compact_fv_empty_0174 : (nb078_alpha_dummy_213) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0542 : (nb078_alpha_dummy_213) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_213, fv_syn_c1c] using (nb078_compact_fv_empty_0174)

theorem nb078_compact_fv_empty_0175 (f : Var) : (nb078_alpha_dummy_214 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0543 (f : Var) : (nb078_alpha_dummy_214 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_214, fv_syn_c1c] using (nb078_compact_fv_empty_0175 f)

theorem nb078_compact_fv_empty_0176 : (nb078_alpha_dummy_211) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0544 : (nb078_alpha_dummy_211) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_211, fv_syn_c1c] using (nb078_compact_fv_empty_0176)

theorem nb078_compact_fv_empty_0177 (f : Var) : (nb078_alpha_dummy_212 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0545 (f : Var) : (nb078_alpha_dummy_212 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_212, fv_syn_c1c] using (nb078_compact_fv_empty_0177 f)

theorem nb078_wpp_notmem_0546 : (nb078_alpha_dummy_204) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_204, fv_syn_c1c] using (nb078_compact_fv_empty_0154)

theorem nb078_wpp_notmem_0547 (f : Var) : (nb078_alpha_dummy_206 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_206, fv_syn_c1c] using (nb078_compact_fv_empty_0155 f)

theorem nb078_wpp_notmem_0548 : (nb078_alpha_dummy_203) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_203, fv_syn_c1c] using (nb078_compact_fv_empty_0156)

theorem nb078_wpp_notmem_0549 (f : Var) : (nb078_alpha_dummy_205 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_205, fv_syn_c1c] using (nb078_compact_fv_empty_0157 f)

theorem nb078_compact_envfresh_0072 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222), (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)), ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_223) (nb078_alpha_dummy_226 f) (nb078_wpp_notmem_0526) (nb078_wpp_notmem_0527 f) (TEnvFresh.consFresh (nb078_alpha_dummy_222) (nb078_alpha_dummy_225 f) (nb078_wpp_notmem_0528) (nb078_wpp_notmem_0529 f) (TEnvFresh.consFresh (nb078_alpha_dummy_221) (nb078_alpha_dummy_224 f) (nb078_wpp_notmem_0530) (nb078_wpp_notmem_0531 f) (TEnvFresh.consFresh (nb078_alpha_dummy_219) (nb078_alpha_dummy_220 f) (nb078_wpp_notmem_0532) (nb078_wpp_notmem_0533 f) (TEnvFresh.consFresh (nb078_alpha_dummy_215) (nb078_alpha_dummy_217 f) (nb078_wpp_notmem_0534) (nb078_wpp_notmem_0535 f) (TEnvFresh.consFresh (nb078_alpha_dummy_216) (nb078_alpha_dummy_218 f) (nb078_wpp_notmem_0536) (nb078_wpp_notmem_0537 f) (TEnvFresh.consFresh (nb078_alpha_dummy_208) (nb078_alpha_dummy_210 f) (nb078_wpp_notmem_0538) (nb078_wpp_notmem_0539 f) (TEnvFresh.consFresh (nb078_alpha_dummy_207) (nb078_alpha_dummy_209 f) (nb078_wpp_notmem_0540) (nb078_wpp_notmem_0541 f) (TEnvFresh.consFresh (nb078_alpha_dummy_213) (nb078_alpha_dummy_214 f) (nb078_wpp_notmem_0542) (nb078_wpp_notmem_0543 f) (TEnvFresh.consFresh (nb078_alpha_dummy_211) (nb078_alpha_dummy_212 f) (nb078_wpp_notmem_0544) (nb078_wpp_notmem_0545 f) (TEnvFresh.consFresh (nb078_alpha_dummy_204) (nb078_alpha_dummy_206 f) (nb078_wpp_notmem_0546) (nb078_wpp_notmem_0547 f) (TEnvFresh.consFresh (nb078_alpha_dummy_203) (nb078_alpha_dummy_205 f) (nb078_wpp_notmem_0548) (nb078_wpp_notmem_0549 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0030) (nb078_wpp_notmem_0031 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0072 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222), (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)), ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0072 x y f)

theorem nb078_wpp_notmem_0550 : (nb078_alpha_dummy_223) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_223, fv_syn_c0] using (nb078_compact_fv_empty_0158)

theorem nb078_wpp_notmem_0551 (f : Var) : (nb078_alpha_dummy_226 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_226, fv_syn_c0] using (nb078_compact_fv_empty_0159 f)

theorem nb078_wpp_notmem_0552 : (nb078_alpha_dummy_222) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_222, fv_syn_c0] using (nb078_compact_fv_empty_0160)

theorem nb078_wpp_notmem_0553 (f : Var) : (nb078_alpha_dummy_225 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_225, fv_syn_c0] using (nb078_compact_fv_empty_0161 f)

theorem nb078_wpp_notmem_0554 : (nb078_alpha_dummy_221) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_221, fv_syn_c0] using (nb078_compact_fv_empty_0162)

theorem nb078_wpp_notmem_0555 (f : Var) : (nb078_alpha_dummy_224 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_224, fv_syn_c0] using (nb078_compact_fv_empty_0163 f)

theorem nb078_wpp_notmem_0556 : (nb078_alpha_dummy_219) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_219, fv_syn_c0] using (nb078_compact_fv_empty_0164)

theorem nb078_wpp_notmem_0557 (f : Var) : (nb078_alpha_dummy_220 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_220, fv_syn_c0] using (nb078_compact_fv_empty_0165 f)

theorem nb078_wpp_notmem_0558 : (nb078_alpha_dummy_215) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_215, fv_syn_c0] using (nb078_compact_fv_empty_0166)

theorem nb078_wpp_notmem_0559 (f : Var) : (nb078_alpha_dummy_217 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_217, fv_syn_c0] using (nb078_compact_fv_empty_0167 f)

theorem nb078_wpp_notmem_0560 : (nb078_alpha_dummy_216) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_216, fv_syn_c0] using (nb078_compact_fv_empty_0168)

theorem nb078_wpp_notmem_0561 (f : Var) : (nb078_alpha_dummy_218 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_218, fv_syn_c0] using (nb078_compact_fv_empty_0169 f)

theorem nb078_wpp_notmem_0562 : (nb078_alpha_dummy_208) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_208, fv_syn_c0] using (nb078_compact_fv_empty_0170)

theorem nb078_wpp_notmem_0563 (f : Var) : (nb078_alpha_dummy_210 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_210, fv_syn_c0] using (nb078_compact_fv_empty_0171 f)

theorem nb078_wpp_notmem_0564 : (nb078_alpha_dummy_207) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_207, fv_syn_c0] using (nb078_compact_fv_empty_0172)

theorem nb078_wpp_notmem_0565 (f : Var) : (nb078_alpha_dummy_209 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_209, fv_syn_c0] using (nb078_compact_fv_empty_0173 f)

theorem nb078_wpp_notmem_0566 : (nb078_alpha_dummy_213) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_213, fv_syn_c0] using (nb078_compact_fv_empty_0174)

theorem nb078_wpp_notmem_0567 (f : Var) : (nb078_alpha_dummy_214 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_214, fv_syn_c0] using (nb078_compact_fv_empty_0175 f)

theorem nb078_wpp_notmem_0568 : (nb078_alpha_dummy_211) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_211, fv_syn_c0] using (nb078_compact_fv_empty_0176)

theorem nb078_wpp_notmem_0569 (f : Var) : (nb078_alpha_dummy_212 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_212, fv_syn_c0] using (nb078_compact_fv_empty_0177 f)

theorem nb078_wpp_notmem_0570 : (nb078_alpha_dummy_204) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_204, fv_syn_c0] using (nb078_compact_fv_empty_0154)

theorem nb078_wpp_notmem_0571 (f : Var) : (nb078_alpha_dummy_206 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_206, fv_syn_c0] using (nb078_compact_fv_empty_0155 f)

theorem nb078_wpp_notmem_0572 : (nb078_alpha_dummy_203) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_203, fv_syn_c0] using (nb078_compact_fv_empty_0156)

theorem nb078_wpp_notmem_0573 (f : Var) : (nb078_alpha_dummy_205 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_205, fv_syn_c0] using (nb078_compact_fv_empty_0157 f)

theorem nb078_compact_envfresh_0073 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222), (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)), ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_223) (nb078_alpha_dummy_226 f) (nb078_wpp_notmem_0550) (nb078_wpp_notmem_0551 f) (TEnvFresh.consFresh (nb078_alpha_dummy_222) (nb078_alpha_dummy_225 f) (nb078_wpp_notmem_0552) (nb078_wpp_notmem_0553 f) (TEnvFresh.consFresh (nb078_alpha_dummy_221) (nb078_alpha_dummy_224 f) (nb078_wpp_notmem_0554) (nb078_wpp_notmem_0555 f) (TEnvFresh.consFresh (nb078_alpha_dummy_219) (nb078_alpha_dummy_220 f) (nb078_wpp_notmem_0556) (nb078_wpp_notmem_0557 f) (TEnvFresh.consFresh (nb078_alpha_dummy_215) (nb078_alpha_dummy_217 f) (nb078_wpp_notmem_0558) (nb078_wpp_notmem_0559 f) (TEnvFresh.consFresh (nb078_alpha_dummy_216) (nb078_alpha_dummy_218 f) (nb078_wpp_notmem_0560) (nb078_wpp_notmem_0561 f) (TEnvFresh.consFresh (nb078_alpha_dummy_208) (nb078_alpha_dummy_210 f) (nb078_wpp_notmem_0562) (nb078_wpp_notmem_0563 f) (TEnvFresh.consFresh (nb078_alpha_dummy_207) (nb078_alpha_dummy_209 f) (nb078_wpp_notmem_0564) (nb078_wpp_notmem_0565 f) (TEnvFresh.consFresh (nb078_alpha_dummy_213) (nb078_alpha_dummy_214 f) (nb078_wpp_notmem_0566) (nb078_wpp_notmem_0567 f) (TEnvFresh.consFresh (nb078_alpha_dummy_211) (nb078_alpha_dummy_212 f) (nb078_wpp_notmem_0568) (nb078_wpp_notmem_0569 f) (TEnvFresh.consFresh (nb078_alpha_dummy_204) (nb078_alpha_dummy_206 f) (nb078_wpp_notmem_0570) (nb078_wpp_notmem_0571 f) (TEnvFresh.consFresh (nb078_alpha_dummy_203) (nb078_alpha_dummy_205 f) (nb078_wpp_notmem_0572) (nb078_wpp_notmem_0573 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0066) (nb078_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0073 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222), (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)), ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0073 x y f)

theorem nb078_wpp_notmem_0574 : (nb078_alpha_dummy_219) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_219, fv_syn_cnnc] using (nb078_compact_fv_empty_0164)

theorem nb078_wpp_notmem_0575 (f : Var) : (nb078_alpha_dummy_220 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_220, fv_syn_cnnc] using (nb078_compact_fv_empty_0165 f)

theorem nb078_wpp_notmem_0576 : (nb078_alpha_dummy_215) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_215, fv_syn_cnnc] using (nb078_compact_fv_empty_0166)

theorem nb078_wpp_notmem_0577 (f : Var) : (nb078_alpha_dummy_217 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_217, fv_syn_cnnc] using (nb078_compact_fv_empty_0167 f)

theorem nb078_wpp_notmem_0578 : (nb078_alpha_dummy_216) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_216, fv_syn_cnnc] using (nb078_compact_fv_empty_0168)

theorem nb078_wpp_notmem_0579 (f : Var) : (nb078_alpha_dummy_218 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_218, fv_syn_cnnc] using (nb078_compact_fv_empty_0169 f)

theorem nb078_wpp_notmem_0580 : (nb078_alpha_dummy_208) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_208, fv_syn_cnnc] using (nb078_compact_fv_empty_0170)

theorem nb078_wpp_notmem_0581 (f : Var) : (nb078_alpha_dummy_210 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_210, fv_syn_cnnc] using (nb078_compact_fv_empty_0171 f)

theorem nb078_wpp_notmem_0582 : (nb078_alpha_dummy_207) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_207, fv_syn_cnnc] using (nb078_compact_fv_empty_0172)

theorem nb078_wpp_notmem_0583 (f : Var) : (nb078_alpha_dummy_209 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_209, fv_syn_cnnc] using (nb078_compact_fv_empty_0173 f)

theorem nb078_wpp_notmem_0584 : (nb078_alpha_dummy_213) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_213, fv_syn_cnnc] using (nb078_compact_fv_empty_0174)

theorem nb078_wpp_notmem_0585 (f : Var) : (nb078_alpha_dummy_214 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_214, fv_syn_cnnc] using (nb078_compact_fv_empty_0175 f)

theorem nb078_wpp_notmem_0586 : (nb078_alpha_dummy_211) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_211, fv_syn_cnnc] using (nb078_compact_fv_empty_0176)

theorem nb078_wpp_notmem_0587 (f : Var) : (nb078_alpha_dummy_212 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_212, fv_syn_cnnc] using (nb078_compact_fv_empty_0177 f)

theorem nb078_wpp_notmem_0588 : (nb078_alpha_dummy_204) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_204, fv_syn_cnnc] using (nb078_compact_fv_empty_0154)

theorem nb078_wpp_notmem_0589 (f : Var) : (nb078_alpha_dummy_206 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_206, fv_syn_cnnc] using (nb078_compact_fv_empty_0155 f)

theorem nb078_wpp_notmem_0590 : (nb078_alpha_dummy_203) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_203, fv_syn_cnnc] using (nb078_compact_fv_empty_0156)

theorem nb078_wpp_notmem_0591 (f : Var) : (nb078_alpha_dummy_205 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_205, fv_syn_cnnc] using (nb078_compact_fv_empty_0157 f)

theorem nb078_compact_envfresh_0074 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_219) (nb078_alpha_dummy_220 f) (nb078_wpp_notmem_0574) (nb078_wpp_notmem_0575 f) (TEnvFresh.consFresh (nb078_alpha_dummy_215) (nb078_alpha_dummy_217 f) (nb078_wpp_notmem_0576) (nb078_wpp_notmem_0577 f) (TEnvFresh.consFresh (nb078_alpha_dummy_216) (nb078_alpha_dummy_218 f) (nb078_wpp_notmem_0578) (nb078_wpp_notmem_0579 f) (TEnvFresh.consFresh (nb078_alpha_dummy_208) (nb078_alpha_dummy_210 f) (nb078_wpp_notmem_0580) (nb078_wpp_notmem_0581 f) (TEnvFresh.consFresh (nb078_alpha_dummy_207) (nb078_alpha_dummy_209 f) (nb078_wpp_notmem_0582) (nb078_wpp_notmem_0583 f) (TEnvFresh.consFresh (nb078_alpha_dummy_213) (nb078_alpha_dummy_214 f) (nb078_wpp_notmem_0584) (nb078_wpp_notmem_0585 f) (TEnvFresh.consFresh (nb078_alpha_dummy_211) (nb078_alpha_dummy_212 f) (nb078_wpp_notmem_0586) (nb078_wpp_notmem_0587 f) (TEnvFresh.consFresh (nb078_alpha_dummy_204) (nb078_alpha_dummy_206 f) (nb078_wpp_notmem_0588) (nb078_wpp_notmem_0589 f) (TEnvFresh.consFresh (nb078_alpha_dummy_203) (nb078_alpha_dummy_205 f) (nb078_wpp_notmem_0590) (nb078_wpp_notmem_0591 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0096) (nb078_wpp_notmem_0097 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb078_wpp_refl_0074 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0074 x y f)

theorem nb078_compact_fv_empty_0178 : (nb078_alpha_dummy_241) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0592 : (nb078_alpha_dummy_241) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_241, fv_syn_c1c] using (nb078_compact_fv_empty_0178)

theorem nb078_compact_fv_empty_0179 (f : Var) : (nb078_alpha_dummy_242 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0593 (f : Var) : (nb078_alpha_dummy_242 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_242, fv_syn_c1c] using (nb078_compact_fv_empty_0179 f)

theorem nb078_compact_fv_empty_0180 : (nb078_alpha_dummy_239) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0594 : (nb078_alpha_dummy_239) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_239, fv_syn_c1c] using (nb078_compact_fv_empty_0180)

theorem nb078_compact_fv_empty_0181 (f : Var) : (nb078_alpha_dummy_240 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0595 (f : Var) : (nb078_alpha_dummy_240 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_240, fv_syn_c1c] using (nb078_compact_fv_empty_0181 f)

theorem nb078_compact_fv_empty_0182 : (nb078_alpha_dummy_237) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0596 : (nb078_alpha_dummy_237) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_237, fv_syn_c1c] using (nb078_compact_fv_empty_0182)

theorem nb078_compact_fv_empty_0183 (f : Var) : (nb078_alpha_dummy_238 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0597 (f : Var) : (nb078_alpha_dummy_238 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_238, fv_syn_c1c] using (nb078_compact_fv_empty_0183 f)

theorem nb078_compact_envfresh_0075 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222), (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)), ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)), ((nb078_alpha_dummy_239), (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_237), (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_223) (nb078_alpha_dummy_226 f) (nb078_wpp_notmem_0526) (nb078_wpp_notmem_0527 f) (TEnvFresh.consFresh (nb078_alpha_dummy_222) (nb078_alpha_dummy_225 f) (nb078_wpp_notmem_0528) (nb078_wpp_notmem_0529 f) (TEnvFresh.consFresh (nb078_alpha_dummy_221) (nb078_alpha_dummy_224 f) (nb078_wpp_notmem_0530) (nb078_wpp_notmem_0531 f) (TEnvFresh.consFresh (nb078_alpha_dummy_219) (nb078_alpha_dummy_220 f) (nb078_wpp_notmem_0532) (nb078_wpp_notmem_0533 f) (TEnvFresh.consFresh (nb078_alpha_dummy_215) (nb078_alpha_dummy_217 f) (nb078_wpp_notmem_0534) (nb078_wpp_notmem_0535 f) (TEnvFresh.consFresh (nb078_alpha_dummy_216) (nb078_alpha_dummy_218 f) (nb078_wpp_notmem_0536) (nb078_wpp_notmem_0537 f) (TEnvFresh.consFresh (nb078_alpha_dummy_241) (nb078_alpha_dummy_242 f) (nb078_wpp_notmem_0592) (nb078_wpp_notmem_0593 f) (TEnvFresh.consFresh (nb078_alpha_dummy_239) (nb078_alpha_dummy_240 f) (nb078_wpp_notmem_0594) (nb078_wpp_notmem_0595 f) (TEnvFresh.consFresh (nb078_alpha_dummy_208) (nb078_alpha_dummy_210 f) (nb078_wpp_notmem_0538) (nb078_wpp_notmem_0539 f) (TEnvFresh.consFresh (nb078_alpha_dummy_207) (nb078_alpha_dummy_209 f) (nb078_wpp_notmem_0540) (nb078_wpp_notmem_0541 f) (TEnvFresh.consFresh (nb078_alpha_dummy_237) (nb078_alpha_dummy_238 f) (nb078_wpp_notmem_0596) (nb078_wpp_notmem_0597 f) (TEnvFresh.consFresh (nb078_alpha_dummy_211) (nb078_alpha_dummy_212 f) (nb078_wpp_notmem_0544) (nb078_wpp_notmem_0545 f) (TEnvFresh.consFresh (nb078_alpha_dummy_204) (nb078_alpha_dummy_206 f) (nb078_wpp_notmem_0546) (nb078_wpp_notmem_0547 f) (TEnvFresh.consFresh (nb078_alpha_dummy_203) (nb078_alpha_dummy_205 f) (nb078_wpp_notmem_0548) (nb078_wpp_notmem_0549 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0030) (nb078_wpp_notmem_0031 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0075 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222), (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)), ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)), ((nb078_alpha_dummy_239), (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_237), (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0075 x y f)

theorem nb078_wpp_notmem_0598 : (nb078_alpha_dummy_241) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_241, fv_syn_c0] using (nb078_compact_fv_empty_0178)

theorem nb078_wpp_notmem_0599 (f : Var) : (nb078_alpha_dummy_242 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_242, fv_syn_c0] using (nb078_compact_fv_empty_0179 f)

theorem nb078_wpp_notmem_0600 : (nb078_alpha_dummy_239) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_239, fv_syn_c0] using (nb078_compact_fv_empty_0180)

theorem nb078_wpp_notmem_0601 (f : Var) : (nb078_alpha_dummy_240 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_240, fv_syn_c0] using (nb078_compact_fv_empty_0181 f)

theorem nb078_wpp_notmem_0602 : (nb078_alpha_dummy_237) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_237, fv_syn_c0] using (nb078_compact_fv_empty_0182)

theorem nb078_wpp_notmem_0603 (f : Var) : (nb078_alpha_dummy_238 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_238, fv_syn_c0] using (nb078_compact_fv_empty_0183 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
