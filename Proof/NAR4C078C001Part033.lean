import NAR4C078C001Part032

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

noncomputable def nb078_split_alpha_0001 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_049)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_049)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_050 f)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_050 f)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0011 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0011 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0041 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0039 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_018))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_020 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0015 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0015 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032), (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)), ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0003 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0019 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0017 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0023 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0021 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0019 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0017 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0023 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0021 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032), (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)), ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0004 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0027 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0025 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0027 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0025 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0031 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0029 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0031 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0029 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0005 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0005 x y f)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0011 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0011 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0041 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0039 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_018))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_020 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0015 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0015 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032), (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)), ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0003 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0019 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0017 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0023 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0021 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0019 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0017 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0023 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0021 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032), (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)), ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0004 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0027 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0025 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0027 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0025 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0031 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0029 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0031 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0029 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0005 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)), ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0005 x y f)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (nb078_wpp_refl_0006 x y f)))))

theorem nb078_compact_fv_empty_0042 : (nb078_alpha_dummy_069) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0146 : (nb078_alpha_dummy_069) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_069, fv_syn_c1c] using (nb078_compact_fv_empty_0042)

theorem nb078_compact_fv_empty_0043 (f : Var) : (nb078_alpha_dummy_072 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0147 (f : Var) : (nb078_alpha_dummy_072 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_072, fv_syn_c1c] using (nb078_compact_fv_empty_0043 f)

theorem nb078_compact_fv_empty_0044 : (nb078_alpha_dummy_068) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0148 : (nb078_alpha_dummy_068) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_068, fv_syn_c1c] using (nb078_compact_fv_empty_0044)

theorem nb078_compact_fv_empty_0045 (f : Var) : (nb078_alpha_dummy_071 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0149 (f : Var) : (nb078_alpha_dummy_071 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_071, fv_syn_c1c] using (nb078_compact_fv_empty_0045 f)

theorem nb078_compact_fv_empty_0046 : (nb078_alpha_dummy_067) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0150 : (nb078_alpha_dummy_067) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_067, fv_syn_c1c] using (nb078_compact_fv_empty_0046)

theorem nb078_compact_fv_empty_0047 (f : Var) : (nb078_alpha_dummy_070 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0151 (f : Var) : (nb078_alpha_dummy_070 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_070, fv_syn_c1c] using (nb078_compact_fv_empty_0047 f)

theorem nb078_compact_fv_empty_0048 : (nb078_alpha_dummy_065) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0152 : (nb078_alpha_dummy_065) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_065, fv_syn_c1c] using (nb078_compact_fv_empty_0048)

theorem nb078_compact_fv_empty_0049 (f : Var) : (nb078_alpha_dummy_066 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0153 (f : Var) : (nb078_alpha_dummy_066 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_066, fv_syn_c1c] using (nb078_compact_fv_empty_0049 f)

theorem nb078_compact_fv_empty_0050 : (nb078_alpha_dummy_061) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0154 : (nb078_alpha_dummy_061) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_061, fv_syn_c1c] using (nb078_compact_fv_empty_0050)

theorem nb078_compact_fv_empty_0051 (f : Var) : (nb078_alpha_dummy_063 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0155 (f : Var) : (nb078_alpha_dummy_063 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_063, fv_syn_c1c] using (nb078_compact_fv_empty_0051 f)

theorem nb078_compact_fv_empty_0052 : (nb078_alpha_dummy_062) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0156 : (nb078_alpha_dummy_062) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_062, fv_syn_c1c] using (nb078_compact_fv_empty_0052)

theorem nb078_compact_fv_empty_0053 (f : Var) : (nb078_alpha_dummy_064 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0157 (f : Var) : (nb078_alpha_dummy_064 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_064, fv_syn_c1c] using (nb078_compact_fv_empty_0053 f)

theorem nb078_compact_fv_empty_0054 : (nb078_alpha_dummy_054) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0158 : (nb078_alpha_dummy_054) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_054, fv_syn_c1c] using (nb078_compact_fv_empty_0054)

theorem nb078_compact_fv_empty_0055 (f : Var) : (nb078_alpha_dummy_056 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0159 (f : Var) : (nb078_alpha_dummy_056 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_056, fv_syn_c1c] using (nb078_compact_fv_empty_0055 f)

theorem nb078_compact_fv_empty_0056 : (nb078_alpha_dummy_053) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0160 : (nb078_alpha_dummy_053) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_053, fv_syn_c1c] using (nb078_compact_fv_empty_0056)

theorem nb078_compact_fv_empty_0057 (f : Var) : (nb078_alpha_dummy_055 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0161 (f : Var) : (nb078_alpha_dummy_055 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_055, fv_syn_c1c] using (nb078_compact_fv_empty_0057 f)

theorem nb078_compact_fv_empty_0058 : (nb078_alpha_dummy_059) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0162 : (nb078_alpha_dummy_059) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_059, fv_syn_c1c] using (nb078_compact_fv_empty_0058)

theorem nb078_compact_fv_empty_0059 (f : Var) : (nb078_alpha_dummy_060 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0163 (f : Var) : (nb078_alpha_dummy_060 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_060, fv_syn_c1c] using (nb078_compact_fv_empty_0059 f)

theorem nb078_compact_fv_empty_0060 : (nb078_alpha_dummy_057) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0164 : (nb078_alpha_dummy_057) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_057, fv_syn_c1c] using (nb078_compact_fv_empty_0060)

theorem nb078_compact_fv_empty_0061 (f : Var) : (nb078_alpha_dummy_058 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0165 (f : Var) : (nb078_alpha_dummy_058 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_058, fv_syn_c1c] using (nb078_compact_fv_empty_0061 f)

theorem nb078_compact_fv_empty_0062 : (nb078_alpha_dummy_011) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0166 : (nb078_alpha_dummy_011) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_011, fv_syn_c1c] using (nb078_compact_fv_empty_0062)

theorem nb078_compact_fv_empty_0063 (f : Var) : (nb078_alpha_dummy_014 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0167 (f : Var) : (nb078_alpha_dummy_014 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_014, fv_syn_c1c] using (nb078_compact_fv_empty_0063 f)

theorem nb078_compact_envfresh_0007 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068), (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)), ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_069) (nb078_alpha_dummy_072 f) (nb078_wpp_notmem_0146) (nb078_wpp_notmem_0147 f) (TEnvFresh.consFresh (nb078_alpha_dummy_068) (nb078_alpha_dummy_071 f) (nb078_wpp_notmem_0148) (nb078_wpp_notmem_0149 f) (TEnvFresh.consFresh (nb078_alpha_dummy_067) (nb078_alpha_dummy_070 f) (nb078_wpp_notmem_0150) (nb078_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb078_alpha_dummy_065) (nb078_alpha_dummy_066 f) (nb078_wpp_notmem_0152) (nb078_wpp_notmem_0153 f) (TEnvFresh.consFresh (nb078_alpha_dummy_061) (nb078_alpha_dummy_063 f) (nb078_wpp_notmem_0154) (nb078_wpp_notmem_0155 f) (TEnvFresh.consFresh (nb078_alpha_dummy_062) (nb078_alpha_dummy_064 f) (nb078_wpp_notmem_0156) (nb078_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb078_alpha_dummy_054) (nb078_alpha_dummy_056 f) (nb078_wpp_notmem_0158) (nb078_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb078_alpha_dummy_053) (nb078_alpha_dummy_055 f) (nb078_wpp_notmem_0160) (nb078_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb078_alpha_dummy_059) (nb078_alpha_dummy_060 f) (nb078_wpp_notmem_0162) (nb078_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb078_alpha_dummy_057) (nb078_alpha_dummy_058 f) (nb078_wpp_notmem_0164) (nb078_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0166) (nb078_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0020) (nb078_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0022) (nb078_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0024) (nb078_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0026) (nb078_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0028) (nb078_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0030) (nb078_wpp_notmem_0031 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0007 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068), (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)), ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0007 x y f)

theorem nb078_wpp_notmem_0168 : (nb078_alpha_dummy_069) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_069, fv_syn_c0] using (nb078_compact_fv_empty_0042)

theorem nb078_wpp_notmem_0169 (f : Var) : (nb078_alpha_dummy_072 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_072, fv_syn_c0] using (nb078_compact_fv_empty_0043 f)

theorem nb078_wpp_notmem_0170 : (nb078_alpha_dummy_068) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_068, fv_syn_c0] using (nb078_compact_fv_empty_0044)

theorem nb078_wpp_notmem_0171 (f : Var) : (nb078_alpha_dummy_071 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_071, fv_syn_c0] using (nb078_compact_fv_empty_0045 f)

theorem nb078_wpp_notmem_0172 : (nb078_alpha_dummy_067) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_067, fv_syn_c0] using (nb078_compact_fv_empty_0046)

theorem nb078_wpp_notmem_0173 (f : Var) : (nb078_alpha_dummy_070 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_070, fv_syn_c0] using (nb078_compact_fv_empty_0047 f)

theorem nb078_wpp_notmem_0174 : (nb078_alpha_dummy_065) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_065, fv_syn_c0] using (nb078_compact_fv_empty_0048)

theorem nb078_wpp_notmem_0175 (f : Var) : (nb078_alpha_dummy_066 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_066, fv_syn_c0] using (nb078_compact_fv_empty_0049 f)

theorem nb078_wpp_notmem_0176 : (nb078_alpha_dummy_061) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_061, fv_syn_c0] using (nb078_compact_fv_empty_0050)

theorem nb078_wpp_notmem_0177 (f : Var) : (nb078_alpha_dummy_063 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_063, fv_syn_c0] using (nb078_compact_fv_empty_0051 f)

theorem nb078_wpp_notmem_0178 : (nb078_alpha_dummy_062) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_062, fv_syn_c0] using (nb078_compact_fv_empty_0052)

theorem nb078_wpp_notmem_0179 (f : Var) : (nb078_alpha_dummy_064 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_064, fv_syn_c0] using (nb078_compact_fv_empty_0053 f)

theorem nb078_wpp_notmem_0180 : (nb078_alpha_dummy_054) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_054, fv_syn_c0] using (nb078_compact_fv_empty_0054)

theorem nb078_wpp_notmem_0181 (f : Var) : (nb078_alpha_dummy_056 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_056, fv_syn_c0] using (nb078_compact_fv_empty_0055 f)

theorem nb078_wpp_notmem_0182 : (nb078_alpha_dummy_053) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_053, fv_syn_c0] using (nb078_compact_fv_empty_0056)

theorem nb078_wpp_notmem_0183 (f : Var) : (nb078_alpha_dummy_055 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_055, fv_syn_c0] using (nb078_compact_fv_empty_0057 f)

theorem nb078_wpp_notmem_0184 : (nb078_alpha_dummy_059) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_059, fv_syn_c0] using (nb078_compact_fv_empty_0058)

theorem nb078_wpp_notmem_0185 (f : Var) : (nb078_alpha_dummy_060 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_060, fv_syn_c0] using (nb078_compact_fv_empty_0059 f)

theorem nb078_wpp_notmem_0186 : (nb078_alpha_dummy_057) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_057, fv_syn_c0] using (nb078_compact_fv_empty_0060)

theorem nb078_wpp_notmem_0187 (f : Var) : (nb078_alpha_dummy_058 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_058, fv_syn_c0] using (nb078_compact_fv_empty_0061 f)

theorem nb078_wpp_notmem_0188 : (nb078_alpha_dummy_011) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_011, fv_syn_c0] using (nb078_compact_fv_empty_0062)

theorem nb078_wpp_notmem_0189 (f : Var) : (nb078_alpha_dummy_014 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_014, fv_syn_c0] using (nb078_compact_fv_empty_0063 f)

theorem nb078_compact_envfresh_0008 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068), (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)), ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_069) (nb078_alpha_dummy_072 f) (nb078_wpp_notmem_0168) (nb078_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb078_alpha_dummy_068) (nb078_alpha_dummy_071 f) (nb078_wpp_notmem_0170) (nb078_wpp_notmem_0171 f) (TEnvFresh.consFresh (nb078_alpha_dummy_067) (nb078_alpha_dummy_070 f) (nb078_wpp_notmem_0172) (nb078_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb078_alpha_dummy_065) (nb078_alpha_dummy_066 f) (nb078_wpp_notmem_0174) (nb078_wpp_notmem_0175 f) (TEnvFresh.consFresh (nb078_alpha_dummy_061) (nb078_alpha_dummy_063 f) (nb078_wpp_notmem_0176) (nb078_wpp_notmem_0177 f) (TEnvFresh.consFresh (nb078_alpha_dummy_062) (nb078_alpha_dummy_064 f) (nb078_wpp_notmem_0178) (nb078_wpp_notmem_0179 f) (TEnvFresh.consFresh (nb078_alpha_dummy_054) (nb078_alpha_dummy_056 f) (nb078_wpp_notmem_0180) (nb078_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb078_alpha_dummy_053) (nb078_alpha_dummy_055 f) (nb078_wpp_notmem_0182) (nb078_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb078_alpha_dummy_059) (nb078_alpha_dummy_060 f) (nb078_wpp_notmem_0184) (nb078_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb078_alpha_dummy_057) (nb078_alpha_dummy_058 f) (nb078_wpp_notmem_0186) (nb078_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0188) (nb078_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0056) (nb078_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0058) (nb078_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0060) (nb078_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0062) (nb078_wpp_notmem_0063 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0064) (nb078_wpp_notmem_0065 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0066) (nb078_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0008 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068), (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)), ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0008 x y f)

theorem nb078_wpp_notmem_0190 : (nb078_alpha_dummy_065) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_065, fv_syn_cnnc] using (nb078_compact_fv_empty_0048)

theorem nb078_wpp_notmem_0191 (f : Var) : (nb078_alpha_dummy_066 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_066, fv_syn_cnnc] using (nb078_compact_fv_empty_0049 f)

theorem nb078_wpp_notmem_0192 : (nb078_alpha_dummy_061) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_061, fv_syn_cnnc] using (nb078_compact_fv_empty_0050)

theorem nb078_wpp_notmem_0193 (f : Var) : (nb078_alpha_dummy_063 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_063, fv_syn_cnnc] using (nb078_compact_fv_empty_0051 f)

theorem nb078_wpp_notmem_0194 : (nb078_alpha_dummy_062) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_062, fv_syn_cnnc] using (nb078_compact_fv_empty_0052)

theorem nb078_wpp_notmem_0195 (f : Var) : (nb078_alpha_dummy_064 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_064, fv_syn_cnnc] using (nb078_compact_fv_empty_0053 f)

theorem nb078_wpp_notmem_0196 : (nb078_alpha_dummy_054) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_054, fv_syn_cnnc] using (nb078_compact_fv_empty_0054)

theorem nb078_wpp_notmem_0197 (f : Var) : (nb078_alpha_dummy_056 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_056, fv_syn_cnnc] using (nb078_compact_fv_empty_0055 f)

theorem nb078_wpp_notmem_0198 : (nb078_alpha_dummy_053) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_053, fv_syn_cnnc] using (nb078_compact_fv_empty_0056)

theorem nb078_wpp_notmem_0199 (f : Var) : (nb078_alpha_dummy_055 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_055, fv_syn_cnnc] using (nb078_compact_fv_empty_0057 f)

theorem nb078_wpp_notmem_0200 : (nb078_alpha_dummy_059) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_059, fv_syn_cnnc] using (nb078_compact_fv_empty_0058)

theorem nb078_wpp_notmem_0201 (f : Var) : (nb078_alpha_dummy_060 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_060, fv_syn_cnnc] using (nb078_compact_fv_empty_0059 f)

theorem nb078_wpp_notmem_0202 : (nb078_alpha_dummy_057) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_057, fv_syn_cnnc] using (nb078_compact_fv_empty_0060)

theorem nb078_wpp_notmem_0203 (f : Var) : (nb078_alpha_dummy_058 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_058, fv_syn_cnnc] using (nb078_compact_fv_empty_0061 f)

theorem nb078_wpp_notmem_0204 : (nb078_alpha_dummy_011) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_011, fv_syn_cnnc] using (nb078_compact_fv_empty_0062)

theorem nb078_wpp_notmem_0205 (f : Var) : (nb078_alpha_dummy_014 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_014, fv_syn_cnnc] using (nb078_compact_fv_empty_0063 f)

theorem nb078_compact_envfresh_0009 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_065) (nb078_alpha_dummy_066 f) (nb078_wpp_notmem_0190) (nb078_wpp_notmem_0191 f) (TEnvFresh.consFresh (nb078_alpha_dummy_061) (nb078_alpha_dummy_063 f) (nb078_wpp_notmem_0192) (nb078_wpp_notmem_0193 f) (TEnvFresh.consFresh (nb078_alpha_dummy_062) (nb078_alpha_dummy_064 f) (nb078_wpp_notmem_0194) (nb078_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb078_alpha_dummy_054) (nb078_alpha_dummy_056 f) (nb078_wpp_notmem_0196) (nb078_wpp_notmem_0197 f) (TEnvFresh.consFresh (nb078_alpha_dummy_053) (nb078_alpha_dummy_055 f) (nb078_wpp_notmem_0198) (nb078_wpp_notmem_0199 f) (TEnvFresh.consFresh (nb078_alpha_dummy_059) (nb078_alpha_dummy_060 f) (nb078_wpp_notmem_0200) (nb078_wpp_notmem_0201 f) (TEnvFresh.consFresh (nb078_alpha_dummy_057) (nb078_alpha_dummy_058 f) (nb078_wpp_notmem_0202) (nb078_wpp_notmem_0203 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0204) (nb078_wpp_notmem_0205 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0086) (nb078_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0088) (nb078_wpp_notmem_0089 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0090) (nb078_wpp_notmem_0091 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0092) (nb078_wpp_notmem_0093 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0094) (nb078_wpp_notmem_0095 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0096) (nb078_wpp_notmem_0097 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb078_wpp_refl_0009 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0009 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
