import NAR4C075C001Part004

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

noncomputable def nb075_split_alpha_0002 (x : Var) : TAlphaWff [((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (Wff.classEq (Class.cv (nb075_alpha_dummy_003)) (syn_cop (Class.cv (nb075_alpha_dummy_000)) (Class.cv (nb075_alpha_dummy_001)))) (Wff.classEq (Class.cv (nb075_alpha_dummy_004 x)) (syn_cop (Class.cv x) (Class.cv (nb075_alpha_dummy_002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0002) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0003 x) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0000) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0001 x) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0011 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0007) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0009 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0012) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0013 x) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0016) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0017 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb075_alpha_dummy_021), (nb075_alpha_dummy_024 x)), ((nb075_alpha_dummy_020), (nb075_alpha_dummy_023 x)), ((nb075_alpha_dummy_019), (nb075_alpha_dummy_022 x)), ((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013), (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)), ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005), (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)), ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_c1c) (nb075_wpp_refl_0000 x))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb075_alpha_dummy_021), (nb075_alpha_dummy_024 x)), ((nb075_alpha_dummy_020), (nb075_alpha_dummy_023 x)), ((nb075_alpha_dummy_019), (nb075_alpha_dummy_022 x)), ((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013), (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)), ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005), (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)), ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_c0) (nb075_wpp_refl_0001 x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013), (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)), ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005), (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)), ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_cnnc) (nb075_wpp_refl_0002 x))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013), (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)), ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005), (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)), ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_cnnc) (nb075_wpp_refl_0002 x)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0006) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0008 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0011 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0007) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0009 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((Class.cv (nb075_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb075_alpha_dummy_002 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0012) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0013 x) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0016) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0017 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb075_alpha_dummy_021), (nb075_alpha_dummy_024 x)), ((nb075_alpha_dummy_020), (nb075_alpha_dummy_023 x)), ((nb075_alpha_dummy_019), (nb075_alpha_dummy_022 x)), ((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013), (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)), ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005), (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)), ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_c1c) (nb075_wpp_refl_0000 x))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0021 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0019 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0025 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0023 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb075_alpha_dummy_021), (nb075_alpha_dummy_024 x)), ((nb075_alpha_dummy_020), (nb075_alpha_dummy_023 x)), ((nb075_alpha_dummy_019), (nb075_alpha_dummy_022 x)), ((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013), (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)), ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005), (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)), ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_c0) (nb075_wpp_refl_0001 x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0029 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0027 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0033 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0031 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013), (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)), ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005), (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)), ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_cnnc) (nb075_wpp_refl_0002 x))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013), (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)), ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005), (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)), ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_cnnc) (nb075_wpp_refl_0002 x)))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb075_split_alpha_0001 x)))))))))))

theorem nb075_wpp_notmem_0106 : (nb075_alpha_dummy_001) ∉ ((syn_cvv)).fv := by
  simpa only [nb075_alpha_dummy_001, fv_syn_cvv] using (nb075_compact_fv_empty_0020)

theorem nb075_wpp_notmem_0107 (x : Var) : (nb075_alpha_dummy_002 x) ∉ ((syn_cvv)).fv := by
  simpa only [nb075_alpha_dummy_002, fv_syn_cvv] using (nb075_compact_fv_empty_0021 x)

theorem nb075_wpp_notmem_0108 : (nb075_alpha_dummy_000) ∉ ((syn_cvv)).fv := by
  simpa only [nb075_alpha_dummy_000, fv_syn_cvv] using (nb075_compact_fv_empty_0022)

theorem nb075_wpp_notmem_0109 (x : Var) : x ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb075_compact_fv_empty_0023 x)

theorem nb075_wpp_notmem_0110 : (nb075_alpha_dummy_003) ∉ ((syn_cvv)).fv := by
  simpa only [nb075_alpha_dummy_003, fv_syn_cvv] using (nb075_compact_fv_empty_0024)

theorem nb075_wpp_notmem_0111 (x : Var) : (nb075_alpha_dummy_004 x) ∉ ((syn_cvv)).fv := by
  simpa only [nb075_alpha_dummy_004, fv_syn_cvv] using (nb075_compact_fv_empty_0025 x)

theorem nb075_compact_envfresh_0007 (x : Var) : TEnvFresh [((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb075_alpha_dummy_001) (nb075_alpha_dummy_002 x) (nb075_wpp_notmem_0106) (nb075_wpp_notmem_0107 x) (TEnvFresh.consFresh (nb075_alpha_dummy_000) x (nb075_wpp_notmem_0108) (nb075_wpp_notmem_0109 x) (TEnvFresh.consFresh (nb075_alpha_dummy_003) (nb075_alpha_dummy_004 x) (nb075_wpp_notmem_0110) (nb075_wpp_notmem_0111 x) (TEnvFresh.nil ((syn_cvv)).fv))))

noncomputable def nb075_wpp_refl_0007 (x : Var) : TReflOn [((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb075_compact_envfresh_0007 x)

theorem nb075_compact_fv_empty_0032 : (nb075_alpha_dummy_042) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0112 : (nb075_alpha_dummy_042) ∉ ((syn_cvv)).fv := by
  simpa only [nb075_alpha_dummy_042, fv_syn_cvv] using (nb075_compact_fv_empty_0032)

theorem nb075_compact_fv_empty_0033 (x : Var) : (nb075_alpha_dummy_044 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0113 (x : Var) : (nb075_alpha_dummy_044 x) ∉ ((syn_cvv)).fv := by
  simpa only [nb075_alpha_dummy_044, fv_syn_cvv] using (nb075_compact_fv_empty_0033 x)

theorem nb075_compact_fv_empty_0034 : (nb075_alpha_dummy_041) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0114 : (nb075_alpha_dummy_041) ∉ ((syn_cvv)).fv := by
  simpa only [nb075_alpha_dummy_041, fv_syn_cvv] using (nb075_compact_fv_empty_0034)

theorem nb075_compact_fv_empty_0035 (x : Var) : (nb075_alpha_dummy_043 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0115 (x : Var) : (nb075_alpha_dummy_043 x) ∉ ((syn_cvv)).fv := by
  simpa only [nb075_alpha_dummy_043, fv_syn_cvv] using (nb075_compact_fv_empty_0035 x)

theorem nb075_compact_envfresh_0008 (x : Var) : TEnvFresh [((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb075_alpha_dummy_042) (nb075_alpha_dummy_044 x) (nb075_wpp_notmem_0112) (nb075_wpp_notmem_0113 x) (TEnvFresh.consFresh (nb075_alpha_dummy_041) (nb075_alpha_dummy_043 x) (nb075_wpp_notmem_0114) (nb075_wpp_notmem_0115 x) (TEnvFresh.consFresh (nb075_alpha_dummy_001) (nb075_alpha_dummy_002 x) (nb075_wpp_notmem_0106) (nb075_wpp_notmem_0107 x) (TEnvFresh.consFresh (nb075_alpha_dummy_000) x (nb075_wpp_notmem_0108) (nb075_wpp_notmem_0109 x) (TEnvFresh.consFresh (nb075_alpha_dummy_003) (nb075_alpha_dummy_004 x) (nb075_wpp_notmem_0110) (nb075_wpp_notmem_0111 x) (TEnvFresh.nil ((syn_cvv)).fv))))))

noncomputable def nb075_wpp_refl_0008 (x : Var) : TReflOn [((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb075_compact_envfresh_0008 x)

theorem nb075_compact_fv_empty_0036 : (nb075_alpha_dummy_061) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0116 : (nb075_alpha_dummy_061) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_061, fv_syn_c1c] using (nb075_compact_fv_empty_0036)

theorem nb075_compact_fv_empty_0037 (x : Var) : (nb075_alpha_dummy_064 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0117 (x : Var) : (nb075_alpha_dummy_064 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_064, fv_syn_c1c] using (nb075_compact_fv_empty_0037 x)

theorem nb075_compact_fv_empty_0038 : (nb075_alpha_dummy_060) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0118 : (nb075_alpha_dummy_060) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_060, fv_syn_c1c] using (nb075_compact_fv_empty_0038)

theorem nb075_compact_fv_empty_0039 (x : Var) : (nb075_alpha_dummy_063 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0119 (x : Var) : (nb075_alpha_dummy_063 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_063, fv_syn_c1c] using (nb075_compact_fv_empty_0039 x)

theorem nb075_compact_fv_empty_0040 : (nb075_alpha_dummy_059) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0120 : (nb075_alpha_dummy_059) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_059, fv_syn_c1c] using (nb075_compact_fv_empty_0040)

theorem nb075_compact_fv_empty_0041 (x : Var) : (nb075_alpha_dummy_062 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0121 (x : Var) : (nb075_alpha_dummy_062 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_062, fv_syn_c1c] using (nb075_compact_fv_empty_0041 x)

theorem nb075_compact_fv_empty_0042 : (nb075_alpha_dummy_057) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0122 : (nb075_alpha_dummy_057) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_057, fv_syn_c1c] using (nb075_compact_fv_empty_0042)

theorem nb075_compact_fv_empty_0043 (x : Var) : (nb075_alpha_dummy_058 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0123 (x : Var) : (nb075_alpha_dummy_058 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_058, fv_syn_c1c] using (nb075_compact_fv_empty_0043 x)

theorem nb075_compact_fv_empty_0044 : (nb075_alpha_dummy_053) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0124 : (nb075_alpha_dummy_053) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_053, fv_syn_c1c] using (nb075_compact_fv_empty_0044)

theorem nb075_compact_fv_empty_0045 (x : Var) : (nb075_alpha_dummy_055 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0125 (x : Var) : (nb075_alpha_dummy_055 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_055, fv_syn_c1c] using (nb075_compact_fv_empty_0045 x)

theorem nb075_compact_fv_empty_0046 : (nb075_alpha_dummy_054) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0126 : (nb075_alpha_dummy_054) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_054, fv_syn_c1c] using (nb075_compact_fv_empty_0046)

theorem nb075_compact_fv_empty_0047 (x : Var) : (nb075_alpha_dummy_056 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0127 (x : Var) : (nb075_alpha_dummy_056 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_056, fv_syn_c1c] using (nb075_compact_fv_empty_0047 x)

theorem nb075_compact_fv_empty_0048 : (nb075_alpha_dummy_046) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0128 : (nb075_alpha_dummy_046) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_046, fv_syn_c1c] using (nb075_compact_fv_empty_0048)

theorem nb075_compact_fv_empty_0049 (x : Var) : (nb075_alpha_dummy_048 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0129 (x : Var) : (nb075_alpha_dummy_048 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_048, fv_syn_c1c] using (nb075_compact_fv_empty_0049 x)

theorem nb075_compact_fv_empty_0050 : (nb075_alpha_dummy_045) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0130 : (nb075_alpha_dummy_045) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_045, fv_syn_c1c] using (nb075_compact_fv_empty_0050)

theorem nb075_compact_fv_empty_0051 (x : Var) : (nb075_alpha_dummy_047 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0131 (x : Var) : (nb075_alpha_dummy_047 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_047, fv_syn_c1c] using (nb075_compact_fv_empty_0051 x)

theorem nb075_compact_fv_empty_0052 : (nb075_alpha_dummy_051) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0132 : (nb075_alpha_dummy_051) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_051, fv_syn_c1c] using (nb075_compact_fv_empty_0052)

theorem nb075_compact_fv_empty_0053 (x : Var) : (nb075_alpha_dummy_052 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0133 (x : Var) : (nb075_alpha_dummy_052 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_052, fv_syn_c1c] using (nb075_compact_fv_empty_0053 x)

theorem nb075_compact_fv_empty_0054 : (nb075_alpha_dummy_049) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0134 : (nb075_alpha_dummy_049) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_049, fv_syn_c1c] using (nb075_compact_fv_empty_0054)

theorem nb075_compact_fv_empty_0055 (x : Var) : (nb075_alpha_dummy_050 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0135 (x : Var) : (nb075_alpha_dummy_050 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_050, fv_syn_c1c] using (nb075_compact_fv_empty_0055 x)

theorem nb075_wpp_notmem_0136 : (nb075_alpha_dummy_042) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_042, fv_syn_c1c] using (nb075_compact_fv_empty_0032)

theorem nb075_wpp_notmem_0137 (x : Var) : (nb075_alpha_dummy_044 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_044, fv_syn_c1c] using (nb075_compact_fv_empty_0033 x)

theorem nb075_wpp_notmem_0138 : (nb075_alpha_dummy_041) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_041, fv_syn_c1c] using (nb075_compact_fv_empty_0034)

theorem nb075_wpp_notmem_0139 (x : Var) : (nb075_alpha_dummy_043 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_043, fv_syn_c1c] using (nb075_compact_fv_empty_0035 x)

theorem nb075_compact_envfresh_0009 (x : Var) : TEnvFresh [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060), (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)), ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb075_alpha_dummy_061) (nb075_alpha_dummy_064 x) (nb075_wpp_notmem_0116) (nb075_wpp_notmem_0117 x) (TEnvFresh.consFresh (nb075_alpha_dummy_060) (nb075_alpha_dummy_063 x) (nb075_wpp_notmem_0118) (nb075_wpp_notmem_0119 x) (TEnvFresh.consFresh (nb075_alpha_dummy_059) (nb075_alpha_dummy_062 x) (nb075_wpp_notmem_0120) (nb075_wpp_notmem_0121 x) (TEnvFresh.consFresh (nb075_alpha_dummy_057) (nb075_alpha_dummy_058 x) (nb075_wpp_notmem_0122) (nb075_wpp_notmem_0123 x) (TEnvFresh.consFresh (nb075_alpha_dummy_053) (nb075_alpha_dummy_055 x) (nb075_wpp_notmem_0124) (nb075_wpp_notmem_0125 x) (TEnvFresh.consFresh (nb075_alpha_dummy_054) (nb075_alpha_dummy_056 x) (nb075_wpp_notmem_0126) (nb075_wpp_notmem_0127 x) (TEnvFresh.consFresh (nb075_alpha_dummy_046) (nb075_alpha_dummy_048 x) (nb075_wpp_notmem_0128) (nb075_wpp_notmem_0129 x) (TEnvFresh.consFresh (nb075_alpha_dummy_045) (nb075_alpha_dummy_047 x) (nb075_wpp_notmem_0130) (nb075_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb075_alpha_dummy_051) (nb075_alpha_dummy_052 x) (nb075_wpp_notmem_0132) (nb075_wpp_notmem_0133 x) (TEnvFresh.consFresh (nb075_alpha_dummy_049) (nb075_alpha_dummy_050 x) (nb075_wpp_notmem_0134) (nb075_wpp_notmem_0135 x) (TEnvFresh.consFresh (nb075_alpha_dummy_042) (nb075_alpha_dummy_044 x) (nb075_wpp_notmem_0136) (nb075_wpp_notmem_0137 x) (TEnvFresh.consFresh (nb075_alpha_dummy_041) (nb075_alpha_dummy_043 x) (nb075_wpp_notmem_0138) (nb075_wpp_notmem_0139 x) (TEnvFresh.consFresh (nb075_alpha_dummy_001) (nb075_alpha_dummy_002 x) (nb075_wpp_notmem_0020) (nb075_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb075_alpha_dummy_000) x (nb075_wpp_notmem_0022) (nb075_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb075_alpha_dummy_003) (nb075_alpha_dummy_004 x) (nb075_wpp_notmem_0024) (nb075_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb075_wpp_refl_0009 (x : Var) : TReflOn [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060), (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)), ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb075_compact_envfresh_0009 x)

theorem nb075_wpp_notmem_0140 : (nb075_alpha_dummy_061) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_061, fv_syn_c0] using (nb075_compact_fv_empty_0036)

theorem nb075_wpp_notmem_0141 (x : Var) : (nb075_alpha_dummy_064 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_064, fv_syn_c0] using (nb075_compact_fv_empty_0037 x)

theorem nb075_wpp_notmem_0142 : (nb075_alpha_dummy_060) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_060, fv_syn_c0] using (nb075_compact_fv_empty_0038)

theorem nb075_wpp_notmem_0143 (x : Var) : (nb075_alpha_dummy_063 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_063, fv_syn_c0] using (nb075_compact_fv_empty_0039 x)

theorem nb075_wpp_notmem_0144 : (nb075_alpha_dummy_059) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_059, fv_syn_c0] using (nb075_compact_fv_empty_0040)

theorem nb075_wpp_notmem_0145 (x : Var) : (nb075_alpha_dummy_062 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_062, fv_syn_c0] using (nb075_compact_fv_empty_0041 x)

theorem nb075_wpp_notmem_0146 : (nb075_alpha_dummy_057) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_057, fv_syn_c0] using (nb075_compact_fv_empty_0042)

theorem nb075_wpp_notmem_0147 (x : Var) : (nb075_alpha_dummy_058 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_058, fv_syn_c0] using (nb075_compact_fv_empty_0043 x)

theorem nb075_wpp_notmem_0148 : (nb075_alpha_dummy_053) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_053, fv_syn_c0] using (nb075_compact_fv_empty_0044)

theorem nb075_wpp_notmem_0149 (x : Var) : (nb075_alpha_dummy_055 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_055, fv_syn_c0] using (nb075_compact_fv_empty_0045 x)

theorem nb075_wpp_notmem_0150 : (nb075_alpha_dummy_054) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_054, fv_syn_c0] using (nb075_compact_fv_empty_0046)

theorem nb075_wpp_notmem_0151 (x : Var) : (nb075_alpha_dummy_056 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_056, fv_syn_c0] using (nb075_compact_fv_empty_0047 x)

theorem nb075_wpp_notmem_0152 : (nb075_alpha_dummy_046) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_046, fv_syn_c0] using (nb075_compact_fv_empty_0048)

theorem nb075_wpp_notmem_0153 (x : Var) : (nb075_alpha_dummy_048 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_048, fv_syn_c0] using (nb075_compact_fv_empty_0049 x)

theorem nb075_wpp_notmem_0154 : (nb075_alpha_dummy_045) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_045, fv_syn_c0] using (nb075_compact_fv_empty_0050)

theorem nb075_wpp_notmem_0155 (x : Var) : (nb075_alpha_dummy_047 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_047, fv_syn_c0] using (nb075_compact_fv_empty_0051 x)

theorem nb075_wpp_notmem_0156 : (nb075_alpha_dummy_051) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_051, fv_syn_c0] using (nb075_compact_fv_empty_0052)

theorem nb075_wpp_notmem_0157 (x : Var) : (nb075_alpha_dummy_052 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_052, fv_syn_c0] using (nb075_compact_fv_empty_0053 x)

theorem nb075_wpp_notmem_0158 : (nb075_alpha_dummy_049) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_049, fv_syn_c0] using (nb075_compact_fv_empty_0054)

theorem nb075_wpp_notmem_0159 (x : Var) : (nb075_alpha_dummy_050 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_050, fv_syn_c0] using (nb075_compact_fv_empty_0055 x)

theorem nb075_wpp_notmem_0160 : (nb075_alpha_dummy_042) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_042, fv_syn_c0] using (nb075_compact_fv_empty_0032)

theorem nb075_wpp_notmem_0161 (x : Var) : (nb075_alpha_dummy_044 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_044, fv_syn_c0] using (nb075_compact_fv_empty_0033 x)

theorem nb075_wpp_notmem_0162 : (nb075_alpha_dummy_041) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_041, fv_syn_c0] using (nb075_compact_fv_empty_0034)

theorem nb075_wpp_notmem_0163 (x : Var) : (nb075_alpha_dummy_043 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_043, fv_syn_c0] using (nb075_compact_fv_empty_0035 x)

theorem nb075_compact_envfresh_0010 (x : Var) : TEnvFresh [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060), (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)), ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb075_alpha_dummy_061) (nb075_alpha_dummy_064 x) (nb075_wpp_notmem_0140) (nb075_wpp_notmem_0141 x) (TEnvFresh.consFresh (nb075_alpha_dummy_060) (nb075_alpha_dummy_063 x) (nb075_wpp_notmem_0142) (nb075_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb075_alpha_dummy_059) (nb075_alpha_dummy_062 x) (nb075_wpp_notmem_0144) (nb075_wpp_notmem_0145 x) (TEnvFresh.consFresh (nb075_alpha_dummy_057) (nb075_alpha_dummy_058 x) (nb075_wpp_notmem_0146) (nb075_wpp_notmem_0147 x) (TEnvFresh.consFresh (nb075_alpha_dummy_053) (nb075_alpha_dummy_055 x) (nb075_wpp_notmem_0148) (nb075_wpp_notmem_0149 x) (TEnvFresh.consFresh (nb075_alpha_dummy_054) (nb075_alpha_dummy_056 x) (nb075_wpp_notmem_0150) (nb075_wpp_notmem_0151 x) (TEnvFresh.consFresh (nb075_alpha_dummy_046) (nb075_alpha_dummy_048 x) (nb075_wpp_notmem_0152) (nb075_wpp_notmem_0153 x) (TEnvFresh.consFresh (nb075_alpha_dummy_045) (nb075_alpha_dummy_047 x) (nb075_wpp_notmem_0154) (nb075_wpp_notmem_0155 x) (TEnvFresh.consFresh (nb075_alpha_dummy_051) (nb075_alpha_dummy_052 x) (nb075_wpp_notmem_0156) (nb075_wpp_notmem_0157 x) (TEnvFresh.consFresh (nb075_alpha_dummy_049) (nb075_alpha_dummy_050 x) (nb075_wpp_notmem_0158) (nb075_wpp_notmem_0159 x) (TEnvFresh.consFresh (nb075_alpha_dummy_042) (nb075_alpha_dummy_044 x) (nb075_wpp_notmem_0160) (nb075_wpp_notmem_0161 x) (TEnvFresh.consFresh (nb075_alpha_dummy_041) (nb075_alpha_dummy_043 x) (nb075_wpp_notmem_0162) (nb075_wpp_notmem_0163 x) (TEnvFresh.consFresh (nb075_alpha_dummy_001) (nb075_alpha_dummy_002 x) (nb075_wpp_notmem_0046) (nb075_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb075_alpha_dummy_000) x (nb075_wpp_notmem_0048) (nb075_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb075_alpha_dummy_003) (nb075_alpha_dummy_004 x) (nb075_wpp_notmem_0050) (nb075_wpp_notmem_0051 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb075_wpp_refl_0010 (x : Var) : TReflOn [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060), (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)), ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb075_compact_envfresh_0010 x)

theorem nb075_wpp_notmem_0164 : (nb075_alpha_dummy_057) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_057, fv_syn_cnnc] using (nb075_compact_fv_empty_0042)

theorem nb075_wpp_notmem_0165 (x : Var) : (nb075_alpha_dummy_058 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_058, fv_syn_cnnc] using (nb075_compact_fv_empty_0043 x)

theorem nb075_wpp_notmem_0166 : (nb075_alpha_dummy_053) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_053, fv_syn_cnnc] using (nb075_compact_fv_empty_0044)

theorem nb075_wpp_notmem_0167 (x : Var) : (nb075_alpha_dummy_055 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_055, fv_syn_cnnc] using (nb075_compact_fv_empty_0045 x)

theorem nb075_wpp_notmem_0168 : (nb075_alpha_dummy_054) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_054, fv_syn_cnnc] using (nb075_compact_fv_empty_0046)

theorem nb075_wpp_notmem_0169 (x : Var) : (nb075_alpha_dummy_056 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_056, fv_syn_cnnc] using (nb075_compact_fv_empty_0047 x)

theorem nb075_wpp_notmem_0170 : (nb075_alpha_dummy_046) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_046, fv_syn_cnnc] using (nb075_compact_fv_empty_0048)

theorem nb075_wpp_notmem_0171 (x : Var) : (nb075_alpha_dummy_048 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_048, fv_syn_cnnc] using (nb075_compact_fv_empty_0049 x)

theorem nb075_wpp_notmem_0172 : (nb075_alpha_dummy_045) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_045, fv_syn_cnnc] using (nb075_compact_fv_empty_0050)

theorem nb075_wpp_notmem_0173 (x : Var) : (nb075_alpha_dummy_047 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_047, fv_syn_cnnc] using (nb075_compact_fv_empty_0051 x)

theorem nb075_wpp_notmem_0174 : (nb075_alpha_dummy_051) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_051, fv_syn_cnnc] using (nb075_compact_fv_empty_0052)

theorem nb075_wpp_notmem_0175 (x : Var) : (nb075_alpha_dummy_052 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_052, fv_syn_cnnc] using (nb075_compact_fv_empty_0053 x)

theorem nb075_wpp_notmem_0176 : (nb075_alpha_dummy_049) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_049, fv_syn_cnnc] using (nb075_compact_fv_empty_0054)

theorem nb075_wpp_notmem_0177 (x : Var) : (nb075_alpha_dummy_050 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_050, fv_syn_cnnc] using (nb075_compact_fv_empty_0055 x)

theorem nb075_wpp_notmem_0178 : (nb075_alpha_dummy_042) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_042, fv_syn_cnnc] using (nb075_compact_fv_empty_0032)

theorem nb075_wpp_notmem_0179 (x : Var) : (nb075_alpha_dummy_044 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_044, fv_syn_cnnc] using (nb075_compact_fv_empty_0033 x)

theorem nb075_wpp_notmem_0180 : (nb075_alpha_dummy_041) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_041, fv_syn_cnnc] using (nb075_compact_fv_empty_0034)

theorem nb075_wpp_notmem_0181 (x : Var) : (nb075_alpha_dummy_043 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb075_alpha_dummy_043, fv_syn_cnnc] using (nb075_compact_fv_empty_0035 x)

theorem nb075_compact_envfresh_0011 (x : Var) : TEnvFresh [((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb075_alpha_dummy_057) (nb075_alpha_dummy_058 x) (nb075_wpp_notmem_0164) (nb075_wpp_notmem_0165 x) (TEnvFresh.consFresh (nb075_alpha_dummy_053) (nb075_alpha_dummy_055 x) (nb075_wpp_notmem_0166) (nb075_wpp_notmem_0167 x) (TEnvFresh.consFresh (nb075_alpha_dummy_054) (nb075_alpha_dummy_056 x) (nb075_wpp_notmem_0168) (nb075_wpp_notmem_0169 x) (TEnvFresh.consFresh (nb075_alpha_dummy_046) (nb075_alpha_dummy_048 x) (nb075_wpp_notmem_0170) (nb075_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb075_alpha_dummy_045) (nb075_alpha_dummy_047 x) (nb075_wpp_notmem_0172) (nb075_wpp_notmem_0173 x) (TEnvFresh.consFresh (nb075_alpha_dummy_051) (nb075_alpha_dummy_052 x) (nb075_wpp_notmem_0174) (nb075_wpp_notmem_0175 x) (TEnvFresh.consFresh (nb075_alpha_dummy_049) (nb075_alpha_dummy_050 x) (nb075_wpp_notmem_0176) (nb075_wpp_notmem_0177 x) (TEnvFresh.consFresh (nb075_alpha_dummy_042) (nb075_alpha_dummy_044 x) (nb075_wpp_notmem_0178) (nb075_wpp_notmem_0179 x) (TEnvFresh.consFresh (nb075_alpha_dummy_041) (nb075_alpha_dummy_043 x) (nb075_wpp_notmem_0180) (nb075_wpp_notmem_0181 x) (TEnvFresh.consFresh (nb075_alpha_dummy_001) (nb075_alpha_dummy_002 x) (nb075_wpp_notmem_0066) (nb075_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb075_alpha_dummy_000) x (nb075_wpp_notmem_0068) (nb075_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb075_alpha_dummy_003) (nb075_alpha_dummy_004 x) (nb075_wpp_notmem_0070) (nb075_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb075_wpp_refl_0011 (x : Var) : TReflOn [((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb075_compact_envfresh_0011 x)

theorem nb075_compact_fv_empty_0056 : (nb075_alpha_dummy_079) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0182 : (nb075_alpha_dummy_079) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_079, fv_syn_c1c] using (nb075_compact_fv_empty_0056)

theorem nb075_compact_fv_empty_0057 (x : Var) : (nb075_alpha_dummy_080 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0183 (x : Var) : (nb075_alpha_dummy_080 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_080, fv_syn_c1c] using (nb075_compact_fv_empty_0057 x)

theorem nb075_compact_fv_empty_0058 : (nb075_alpha_dummy_077) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0184 : (nb075_alpha_dummy_077) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_077, fv_syn_c1c] using (nb075_compact_fv_empty_0058)

theorem nb075_compact_fv_empty_0059 (x : Var) : (nb075_alpha_dummy_078 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0185 (x : Var) : (nb075_alpha_dummy_078 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_078, fv_syn_c1c] using (nb075_compact_fv_empty_0059 x)

theorem nb075_compact_fv_empty_0060 : (nb075_alpha_dummy_075) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0186 : (nb075_alpha_dummy_075) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_075, fv_syn_c1c] using (nb075_compact_fv_empty_0060)

theorem nb075_compact_fv_empty_0061 (x : Var) : (nb075_alpha_dummy_076 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb075_wpp_notmem_0187 (x : Var) : (nb075_alpha_dummy_076 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb075_alpha_dummy_076, fv_syn_c1c] using (nb075_compact_fv_empty_0061 x)

theorem nb075_compact_envfresh_0012 (x : Var) : TEnvFresh [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060), (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)), ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)), ((nb075_alpha_dummy_077), (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_075), (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb075_alpha_dummy_061) (nb075_alpha_dummy_064 x) (nb075_wpp_notmem_0116) (nb075_wpp_notmem_0117 x) (TEnvFresh.consFresh (nb075_alpha_dummy_060) (nb075_alpha_dummy_063 x) (nb075_wpp_notmem_0118) (nb075_wpp_notmem_0119 x) (TEnvFresh.consFresh (nb075_alpha_dummy_059) (nb075_alpha_dummy_062 x) (nb075_wpp_notmem_0120) (nb075_wpp_notmem_0121 x) (TEnvFresh.consFresh (nb075_alpha_dummy_057) (nb075_alpha_dummy_058 x) (nb075_wpp_notmem_0122) (nb075_wpp_notmem_0123 x) (TEnvFresh.consFresh (nb075_alpha_dummy_053) (nb075_alpha_dummy_055 x) (nb075_wpp_notmem_0124) (nb075_wpp_notmem_0125 x) (TEnvFresh.consFresh (nb075_alpha_dummy_054) (nb075_alpha_dummy_056 x) (nb075_wpp_notmem_0126) (nb075_wpp_notmem_0127 x) (TEnvFresh.consFresh (nb075_alpha_dummy_079) (nb075_alpha_dummy_080 x) (nb075_wpp_notmem_0182) (nb075_wpp_notmem_0183 x) (TEnvFresh.consFresh (nb075_alpha_dummy_077) (nb075_alpha_dummy_078 x) (nb075_wpp_notmem_0184) (nb075_wpp_notmem_0185 x) (TEnvFresh.consFresh (nb075_alpha_dummy_046) (nb075_alpha_dummy_048 x) (nb075_wpp_notmem_0128) (nb075_wpp_notmem_0129 x) (TEnvFresh.consFresh (nb075_alpha_dummy_045) (nb075_alpha_dummy_047 x) (nb075_wpp_notmem_0130) (nb075_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb075_alpha_dummy_075) (nb075_alpha_dummy_076 x) (nb075_wpp_notmem_0186) (nb075_wpp_notmem_0187 x) (TEnvFresh.consFresh (nb075_alpha_dummy_049) (nb075_alpha_dummy_050 x) (nb075_wpp_notmem_0134) (nb075_wpp_notmem_0135 x) (TEnvFresh.consFresh (nb075_alpha_dummy_042) (nb075_alpha_dummy_044 x) (nb075_wpp_notmem_0136) (nb075_wpp_notmem_0137 x) (TEnvFresh.consFresh (nb075_alpha_dummy_041) (nb075_alpha_dummy_043 x) (nb075_wpp_notmem_0138) (nb075_wpp_notmem_0139 x) (TEnvFresh.consFresh (nb075_alpha_dummy_001) (nb075_alpha_dummy_002 x) (nb075_wpp_notmem_0020) (nb075_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb075_alpha_dummy_000) x (nb075_wpp_notmem_0022) (nb075_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb075_alpha_dummy_003) (nb075_alpha_dummy_004 x) (nb075_wpp_notmem_0024) (nb075_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb075_wpp_refl_0012 (x : Var) : TReflOn [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060), (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)), ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)), ((nb075_alpha_dummy_077), (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_075), (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb075_compact_envfresh_0012 x)

theorem nb075_wpp_notmem_0188 : (nb075_alpha_dummy_079) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_079, fv_syn_c0] using (nb075_compact_fv_empty_0056)

theorem nb075_wpp_notmem_0189 (x : Var) : (nb075_alpha_dummy_080 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_080, fv_syn_c0] using (nb075_compact_fv_empty_0057 x)

theorem nb075_wpp_notmem_0190 : (nb075_alpha_dummy_077) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_077, fv_syn_c0] using (nb075_compact_fv_empty_0058)

theorem nb075_wpp_notmem_0191 (x : Var) : (nb075_alpha_dummy_078 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_078, fv_syn_c0] using (nb075_compact_fv_empty_0059 x)

theorem nb075_wpp_notmem_0192 : (nb075_alpha_dummy_075) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_075, fv_syn_c0] using (nb075_compact_fv_empty_0060)

theorem nb075_wpp_notmem_0193 (x : Var) : (nb075_alpha_dummy_076 x) ∉ ((syn_c0)).fv := by
  simpa only [nb075_alpha_dummy_076, fv_syn_c0] using (nb075_compact_fv_empty_0061 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
