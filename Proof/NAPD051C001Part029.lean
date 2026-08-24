import NAPD051C001Part028

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

noncomputable def nominal_df_mpt2
    (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_C_z : z ∉ C.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.classEq (syn_cmpt2 x A y B C) (syn_coprab x y z (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv z) C)))) := by
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (nb051_split_alpha_0004 x y z A B C dv_x_z dv_y_z) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.refl_of_reflOn [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (nb051_wpp_refl_0008 x y z A B C dv_A_z dv_B_z dv_x_z dv_y_z)) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] C (nb051_wpp_refl_0009 x y z A B C dv_C_z)))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
