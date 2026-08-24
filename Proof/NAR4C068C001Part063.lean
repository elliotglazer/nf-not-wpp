import NAR4C068C001Part062

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

noncomputable def nominal_df_en
    (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cen) (syn_copab x y (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y))))) := by
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (nb068_split_alpha_0004 x y f dv_x_y) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.neg (nb068_split_alpha_0192 x y f dv_f_x dv_f_y dv_x_y)) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.neg (nb068_split_alpha_0077 x y f dv_f_x dv_x_y)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cvv) (nb068_wpp_refl_0108 x y f))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0296) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0297 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0293) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0295 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb068_split_alpha_0085 x y f))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0296) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0297 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0293) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0295 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb068_split_alpha_0085 x y f))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0088 x y f)))))))))) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0334) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0335 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0334) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0335 f) 0)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_f_y) (TAlphaVar.here _ _ _)))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
