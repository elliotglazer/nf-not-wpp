import NAR5H088P001Part004

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

noncomputable def nb088_split_alpha_0002 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : TAlphaWff [((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (Wff.classEq (Class.cv (nb088_alpha_dummy_003 A B C R)) (syn_cop (Class.cv (nb088_alpha_dummy_000 A B C R)) (Class.cv (nb088_alpha_dummy_001 A B C R)))) (Wff.classEq (Class.cv (nb088_alpha_dummy_004 u A B C R)) (syn_cop (Class.cv u) (Class.cv (nb088_alpha_dummy_002 u A B C R)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0002 A B C R) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0003 u A B C R) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0000 A B C R) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0001 u A B C R) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0010 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0011 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0007 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0009 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0004 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0005 u A B C R) 0)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_000 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_001 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb088_alpha_dummy_002 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0012 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0013 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0012 A B C R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0013 u A B C R) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_006 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_008 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0016 A B C R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0017 u A B C R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0016 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0017 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0014 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0015 u A B C R) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb088_alpha_dummy_021 A B C R), (nb088_alpha_dummy_024 u A B C R)), ((nb088_alpha_dummy_020 A B C R), (nb088_alpha_dummy_023 u A B C R)), ((nb088_alpha_dummy_019 A B C R), (nb088_alpha_dummy_022 u A B C R)), ((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)), ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)), ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)), ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)), ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)), ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)), ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (nb088_wpp_refl_0000 u A B C R))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0020 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0021 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0018 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0019 u A B C R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0024 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0025 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0022 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0023 u A B C R) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0020 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0021 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0018 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0019 u A B C R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0024 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0025 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0022 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0023 u A B C R) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb088_alpha_dummy_021 A B C R), (nb088_alpha_dummy_024 u A B C R)), ((nb088_alpha_dummy_020 A B C R), (nb088_alpha_dummy_023 u A B C R)), ((nb088_alpha_dummy_019 A B C R), (nb088_alpha_dummy_022 u A B C R)), ((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)), ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)), ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)), ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)), ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)), ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)), ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (nb088_wpp_refl_0001 u A B C R))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0028 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0029 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0026 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0027 u A B C R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0028 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0029 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0026 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0027 u A B C R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0032 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0033 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0030 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0031 u A B C R) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0032 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0033 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0030 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0031 u A B C R) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0014 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0015 u A B C R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)), ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)), ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)), ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)), ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)), ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)), ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (nb088_wpp_refl_0002 u A B C R))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0014 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0015 u A B C R) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0014 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0015 u A B C R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)), ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)), ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)), ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)), ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)), ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)), ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (nb088_wpp_refl_0002 u A B C R)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0010 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0011 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0007 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0009 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0004 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0005 u A B C R) 0)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_000 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_001 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb088_alpha_dummy_002 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0012 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0013 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0012 A B C R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0013 u A B C R) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_006 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_008 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0016 A B C R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0017 u A B C R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0016 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0017 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0014 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0015 u A B C R) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb088_alpha_dummy_021 A B C R), (nb088_alpha_dummy_024 u A B C R)), ((nb088_alpha_dummy_020 A B C R), (nb088_alpha_dummy_023 u A B C R)), ((nb088_alpha_dummy_019 A B C R), (nb088_alpha_dummy_022 u A B C R)), ((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)), ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)), ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)), ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)), ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)), ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)), ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (nb088_wpp_refl_0000 u A B C R))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0020 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0021 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0018 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0019 u A B C R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0024 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0025 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0022 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0023 u A B C R) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0020 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0021 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0018 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0019 u A B C R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0024 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0025 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0022 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0023 u A B C R) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb088_alpha_dummy_021 A B C R), (nb088_alpha_dummy_024 u A B C R)), ((nb088_alpha_dummy_020 A B C R), (nb088_alpha_dummy_023 u A B C R)), ((nb088_alpha_dummy_019 A B C R), (nb088_alpha_dummy_022 u A B C R)), ((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)), ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)), ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)), ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)), ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)), ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)), ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (nb088_wpp_refl_0001 u A B C R))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0028 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0029 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0026 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0027 u A B C R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0028 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0029 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0026 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0027 u A B C R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0032 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0033 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0030 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0031 u A B C R) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0032 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0033 u A B C R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0030 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0031 u A B C R) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0014 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0015 u A B C R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)), ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)), ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)), ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)), ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)), ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)), ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (nb088_wpp_refl_0002 u A B C R))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0014 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0015 u A B C R) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0014 A B C R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0015 u A B C R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)), ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)), ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)), ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)), ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)), ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)), ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (nb088_wpp_refl_0002 u A B C R)))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb088_split_alpha_0001 u A B C R)))))))))))

theorem nb088_focused_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_001 A B C R) ∉ C.fv := by
  change freshVar (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪ ((syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 C)).symm ▸ (((fv_syn_cpw1 C).symm ▸ (hu)))))))

theorem nb088_wpp_notmem_0106 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_001 A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_001, fv_syn_cpw1] using (nb088_focused_notmem_0000 A B C R)

theorem nb088_focused_notmem_0001 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∉ C.fv := by
  change freshVar (({u} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪ ((syn_cfdrowfib R A B (Class.cv u))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 C)).symm ▸ (((fv_syn_cpw1 C).symm ▸ (hu)))))))

theorem nb088_wpp_notmem_0107 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_002, fv_syn_cpw1] using (nb088_focused_notmem_0001 u A B C R)

theorem nb088_focused_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∉ C.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb088_wpp_notmem_0108 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_000, fv_syn_cpw1] using (nb088_focused_notmem_0002 A B C R)

theorem nb088_wpp_notmem_0109 (u : Var) (C : Class) (dv_C_u : u ∉ C.fv) : u ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [fv_syn_cpw1] using dv_C_u

theorem nb088_focused_notmem_0003 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_003 A B C R) ∉ C.fv := by
  change freshVar (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ({(nb088_alpha_dummy_001 A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R)) (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R)) (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 C)).symm ▸ (((fv_syn_cpw1 C).symm ▸ (hu))))))))))))

theorem nb088_wpp_notmem_0110 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_003 A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_003, fv_syn_cpw1] using (nb088_focused_notmem_0003 A B C R)

theorem nb088_focused_notmem_0004 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_004 u A B C R) ∉ C.fv := by
  change freshVar (({u} : Finset Var) ∪ ({(nb088_alpha_dummy_002 u A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R)) (syn_cfdrowfib R A B (Class.cv u)))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 C)).symm ▸ (((fv_syn_cpw1 C).symm ▸ (hu))))))))))))

theorem nb088_wpp_notmem_0111 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_004 u A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_004, fv_syn_cpw1] using (nb088_focused_notmem_0004 u A B C R)

theorem nb088_compact_envfresh_0007 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) (dv_C_u : u ∉ C.fv) : TEnvFresh [((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] ((syn_cpw1 (syn_cpw1 C))).fv := by
  exact (TEnvFresh.consFresh (nb088_alpha_dummy_001 A B C R) (nb088_alpha_dummy_002 u A B C R) (nb088_wpp_notmem_0106 A B C R) (nb088_wpp_notmem_0107 u A B C R) (TEnvFresh.consFresh (nb088_alpha_dummy_000 A B C R) u (nb088_wpp_notmem_0108 A B C R) (nb088_wpp_notmem_0109 u C dv_C_u) (TEnvFresh.consFresh (nb088_alpha_dummy_003 A B C R) (nb088_alpha_dummy_004 u A B C R) (nb088_wpp_notmem_0110 A B C R) (nb088_wpp_notmem_0111 u A B C R) (TEnvFresh.nil ((syn_cpw1 (syn_cpw1 C))).fv))))

noncomputable def nb088_wpp_refl_0007 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) (dv_C_u : u ∉ C.fv) : TReflOn [((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] ((syn_cpw1 (syn_cpw1 C))).fv :=
  TEnvFresh.reflOn (nb088_compact_envfresh_0007 u A B C R dv_C_u)

theorem nb088_compact_fv_empty_0032 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_061 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0112 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_061 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_061, fv_syn_c1c] using (nb088_compact_fv_empty_0032 A B C R)

theorem nb088_compact_fv_empty_0033 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_064 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0113 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_064 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_064, fv_syn_c1c] using (nb088_compact_fv_empty_0033 u A B R)

theorem nb088_compact_fv_empty_0034 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_060 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0114 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_060 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_060, fv_syn_c1c] using (nb088_compact_fv_empty_0034 A B C R)

theorem nb088_compact_fv_empty_0035 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_063 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0115 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_063 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_063, fv_syn_c1c] using (nb088_compact_fv_empty_0035 u A B R)

theorem nb088_compact_fv_empty_0036 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_059 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0116 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_059 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_059, fv_syn_c1c] using (nb088_compact_fv_empty_0036 A B C R)

theorem nb088_compact_fv_empty_0037 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_062 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0117 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_062 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_062, fv_syn_c1c] using (nb088_compact_fv_empty_0037 u A B R)

theorem nb088_compact_fv_empty_0038 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_057 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0118 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_057 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_057, fv_syn_c1c] using (nb088_compact_fv_empty_0038 A B C R)

theorem nb088_compact_fv_empty_0039 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_058 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0119 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_058 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_058, fv_syn_c1c] using (nb088_compact_fv_empty_0039 u A B R)

theorem nb088_compact_fv_empty_0040 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_053 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0120 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_053 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_053, fv_syn_c1c] using (nb088_compact_fv_empty_0040 A B C R)

theorem nb088_compact_fv_empty_0041 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_055 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0121 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_055 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_055, fv_syn_c1c] using (nb088_compact_fv_empty_0041 u A B R)

theorem nb088_compact_fv_empty_0042 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_054 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0122 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_054 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_054, fv_syn_c1c] using (nb088_compact_fv_empty_0042 A B C R)

theorem nb088_compact_fv_empty_0043 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_056 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0123 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_056 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_056, fv_syn_c1c] using (nb088_compact_fv_empty_0043 u A B R)

theorem nb088_compact_fv_empty_0044 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_044 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0124 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_044 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_044, fv_syn_c1c] using (nb088_compact_fv_empty_0044 A B C R)

theorem nb088_compact_fv_empty_0045 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_046 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0125 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_046 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_046, fv_syn_c1c] using (nb088_compact_fv_empty_0045 u A B R)

theorem nb088_compact_fv_empty_0046 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_043 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0126 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_043 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_043, fv_syn_c1c] using (nb088_compact_fv_empty_0046 A B C R)

theorem nb088_compact_fv_empty_0047 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_045 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0127 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_045 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_045, fv_syn_c1c] using (nb088_compact_fv_empty_0047 u A B R)

theorem nb088_compact_fv_empty_0048 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_049 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0128 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_049 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_049, fv_syn_c1c] using (nb088_compact_fv_empty_0048 A B C R)

theorem nb088_compact_fv_empty_0049 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_050 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0129 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_050 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_050, fv_syn_c1c] using (nb088_compact_fv_empty_0049 u A B R)

theorem nb088_compact_fv_empty_0050 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_047 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0130 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_047 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_047, fv_syn_c1c] using (nb088_compact_fv_empty_0050 A B C R)

theorem nb088_compact_fv_empty_0051 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_048 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0131 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_048 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_048, fv_syn_c1c] using (nb088_compact_fv_empty_0051 u A B R)

theorem nb088_compact_fv_empty_0052 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_041 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0132 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_041 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_041, fv_syn_c1c] using (nb088_compact_fv_empty_0052 A B C R)

theorem nb088_compact_fv_empty_0053 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_042 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0133 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_042 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_042, fv_syn_c1c] using (nb088_compact_fv_empty_0053 u A B R)

theorem nb088_compact_envfresh_0008 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : TEnvFresh [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)), ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)), ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)), ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)), ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)), ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)), ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)), ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)), ((nb088_alpha_dummy_049 A B C R), (nb088_alpha_dummy_050 u A B R)), ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)), ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb088_alpha_dummy_061 A B C R) (nb088_alpha_dummy_064 u A B R) (nb088_wpp_notmem_0112 A B C R) (nb088_wpp_notmem_0113 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_060 A B C R) (nb088_alpha_dummy_063 u A B R) (nb088_wpp_notmem_0114 A B C R) (nb088_wpp_notmem_0115 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_059 A B C R) (nb088_alpha_dummy_062 u A B R) (nb088_wpp_notmem_0116 A B C R) (nb088_wpp_notmem_0117 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_057 A B C R) (nb088_alpha_dummy_058 u A B R) (nb088_wpp_notmem_0118 A B C R) (nb088_wpp_notmem_0119 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_053 A B C R) (nb088_alpha_dummy_055 u A B R) (nb088_wpp_notmem_0120 A B C R) (nb088_wpp_notmem_0121 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_054 A B C R) (nb088_alpha_dummy_056 u A B R) (nb088_wpp_notmem_0122 A B C R) (nb088_wpp_notmem_0123 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_044 A B C R) (nb088_alpha_dummy_046 u A B R) (nb088_wpp_notmem_0124 A B C R) (nb088_wpp_notmem_0125 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_043 A B C R) (nb088_alpha_dummy_045 u A B R) (nb088_wpp_notmem_0126 A B C R) (nb088_wpp_notmem_0127 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_049 A B C R) (nb088_alpha_dummy_050 u A B R) (nb088_wpp_notmem_0128 A B C R) (nb088_wpp_notmem_0129 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_047 A B C R) (nb088_alpha_dummy_048 u A B R) (nb088_wpp_notmem_0130 A B C R) (nb088_wpp_notmem_0131 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_041 A B C R) (nb088_alpha_dummy_042 u A B R) (nb088_wpp_notmem_0132 A B C R) (nb088_wpp_notmem_0133 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_001 A B C R) (nb088_alpha_dummy_002 u A B C R) (nb088_wpp_notmem_0020 A B C R) (nb088_wpp_notmem_0021 u A B C R) (TEnvFresh.consFresh (nb088_alpha_dummy_000 A B C R) u (nb088_wpp_notmem_0022 A B C R) (nb088_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb088_alpha_dummy_003 A B C R) (nb088_alpha_dummy_004 u A B C R) (nb088_wpp_notmem_0024 A B C R) (nb088_wpp_notmem_0025 u A B C R) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))

noncomputable def nb088_wpp_refl_0008 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : TReflOn [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)), ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)), ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)), ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)), ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)), ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)), ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)), ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)), ((nb088_alpha_dummy_049 A B C R), (nb088_alpha_dummy_050 u A B R)), ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)), ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb088_compact_envfresh_0008 u A B C R)

theorem nb088_wpp_notmem_0134 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_061 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_061, fv_syn_c0] using (nb088_compact_fv_empty_0032 A B C R)

theorem nb088_wpp_notmem_0135 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_064 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_064, fv_syn_c0] using (nb088_compact_fv_empty_0033 u A B R)

theorem nb088_wpp_notmem_0136 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_060 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_060, fv_syn_c0] using (nb088_compact_fv_empty_0034 A B C R)

theorem nb088_wpp_notmem_0137 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_063 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_063, fv_syn_c0] using (nb088_compact_fv_empty_0035 u A B R)

theorem nb088_wpp_notmem_0138 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_059 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_059, fv_syn_c0] using (nb088_compact_fv_empty_0036 A B C R)

theorem nb088_wpp_notmem_0139 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_062 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_062, fv_syn_c0] using (nb088_compact_fv_empty_0037 u A B R)

theorem nb088_wpp_notmem_0140 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_057 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_057, fv_syn_c0] using (nb088_compact_fv_empty_0038 A B C R)

theorem nb088_wpp_notmem_0141 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_058 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_058, fv_syn_c0] using (nb088_compact_fv_empty_0039 u A B R)

theorem nb088_wpp_notmem_0142 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_053 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_053, fv_syn_c0] using (nb088_compact_fv_empty_0040 A B C R)

theorem nb088_wpp_notmem_0143 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_055 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_055, fv_syn_c0] using (nb088_compact_fv_empty_0041 u A B R)

theorem nb088_wpp_notmem_0144 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_054 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_054, fv_syn_c0] using (nb088_compact_fv_empty_0042 A B C R)

theorem nb088_wpp_notmem_0145 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_056 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_056, fv_syn_c0] using (nb088_compact_fv_empty_0043 u A B R)

theorem nb088_wpp_notmem_0146 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_044 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_044, fv_syn_c0] using (nb088_compact_fv_empty_0044 A B C R)

theorem nb088_wpp_notmem_0147 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_046 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_046, fv_syn_c0] using (nb088_compact_fv_empty_0045 u A B R)

theorem nb088_wpp_notmem_0148 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_043 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_043, fv_syn_c0] using (nb088_compact_fv_empty_0046 A B C R)

theorem nb088_wpp_notmem_0149 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_045 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_045, fv_syn_c0] using (nb088_compact_fv_empty_0047 u A B R)

theorem nb088_wpp_notmem_0150 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_049 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_049, fv_syn_c0] using (nb088_compact_fv_empty_0048 A B C R)

theorem nb088_wpp_notmem_0151 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_050 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_050, fv_syn_c0] using (nb088_compact_fv_empty_0049 u A B R)

theorem nb088_wpp_notmem_0152 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_047 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_047, fv_syn_c0] using (nb088_compact_fv_empty_0050 A B C R)

theorem nb088_wpp_notmem_0153 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_048 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_048, fv_syn_c0] using (nb088_compact_fv_empty_0051 u A B R)

theorem nb088_wpp_notmem_0154 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_041 A B C R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_041, fv_syn_c0] using (nb088_compact_fv_empty_0052 A B C R)

theorem nb088_wpp_notmem_0155 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_042 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb088_alpha_dummy_042, fv_syn_c0] using (nb088_compact_fv_empty_0053 u A B R)

theorem nb088_compact_envfresh_0009 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : TEnvFresh [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)), ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)), ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)), ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)), ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)), ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)), ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)), ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)), ((nb088_alpha_dummy_049 A B C R), (nb088_alpha_dummy_050 u A B R)), ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)), ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb088_alpha_dummy_061 A B C R) (nb088_alpha_dummy_064 u A B R) (nb088_wpp_notmem_0134 A B C R) (nb088_wpp_notmem_0135 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_060 A B C R) (nb088_alpha_dummy_063 u A B R) (nb088_wpp_notmem_0136 A B C R) (nb088_wpp_notmem_0137 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_059 A B C R) (nb088_alpha_dummy_062 u A B R) (nb088_wpp_notmem_0138 A B C R) (nb088_wpp_notmem_0139 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_057 A B C R) (nb088_alpha_dummy_058 u A B R) (nb088_wpp_notmem_0140 A B C R) (nb088_wpp_notmem_0141 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_053 A B C R) (nb088_alpha_dummy_055 u A B R) (nb088_wpp_notmem_0142 A B C R) (nb088_wpp_notmem_0143 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_054 A B C R) (nb088_alpha_dummy_056 u A B R) (nb088_wpp_notmem_0144 A B C R) (nb088_wpp_notmem_0145 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_044 A B C R) (nb088_alpha_dummy_046 u A B R) (nb088_wpp_notmem_0146 A B C R) (nb088_wpp_notmem_0147 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_043 A B C R) (nb088_alpha_dummy_045 u A B R) (nb088_wpp_notmem_0148 A B C R) (nb088_wpp_notmem_0149 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_049 A B C R) (nb088_alpha_dummy_050 u A B R) (nb088_wpp_notmem_0150 A B C R) (nb088_wpp_notmem_0151 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_047 A B C R) (nb088_alpha_dummy_048 u A B R) (nb088_wpp_notmem_0152 A B C R) (nb088_wpp_notmem_0153 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_041 A B C R) (nb088_alpha_dummy_042 u A B R) (nb088_wpp_notmem_0154 A B C R) (nb088_wpp_notmem_0155 u A B R) (TEnvFresh.consFresh (nb088_alpha_dummy_001 A B C R) (nb088_alpha_dummy_002 u A B C R) (nb088_wpp_notmem_0046 A B C R) (nb088_wpp_notmem_0047 u A B C R) (TEnvFresh.consFresh (nb088_alpha_dummy_000 A B C R) u (nb088_wpp_notmem_0048 A B C R) (nb088_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb088_alpha_dummy_003 A B C R) (nb088_alpha_dummy_004 u A B C R) (nb088_wpp_notmem_0050 A B C R) (nb088_wpp_notmem_0051 u A B C R) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))

noncomputable def nb088_wpp_refl_0009 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : TReflOn [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)), ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)), ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)), ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)), ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)), ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)), ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)), ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)), ((nb088_alpha_dummy_049 A B C R), (nb088_alpha_dummy_050 u A B R)), ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)), ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)), ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb088_compact_envfresh_0009 u A B C R)

theorem nb088_wpp_notmem_0156 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_057 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_057, fv_syn_cnnc] using (nb088_compact_fv_empty_0038 A B C R)

theorem nb088_wpp_notmem_0157 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_058 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_058, fv_syn_cnnc] using (nb088_compact_fv_empty_0039 u A B R)

theorem nb088_wpp_notmem_0158 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_053 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_053, fv_syn_cnnc] using (nb088_compact_fv_empty_0040 A B C R)

theorem nb088_wpp_notmem_0159 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_055 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_055, fv_syn_cnnc] using (nb088_compact_fv_empty_0041 u A B R)

theorem nb088_wpp_notmem_0160 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_054 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_054, fv_syn_cnnc] using (nb088_compact_fv_empty_0042 A B C R)

theorem nb088_wpp_notmem_0161 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_056 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_056, fv_syn_cnnc] using (nb088_compact_fv_empty_0043 u A B R)

theorem nb088_wpp_notmem_0162 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_044 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_044, fv_syn_cnnc] using (nb088_compact_fv_empty_0044 A B C R)

theorem nb088_wpp_notmem_0163 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_046 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_046, fv_syn_cnnc] using (nb088_compact_fv_empty_0045 u A B R)

theorem nb088_wpp_notmem_0164 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_043 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_043, fv_syn_cnnc] using (nb088_compact_fv_empty_0046 A B C R)

theorem nb088_wpp_notmem_0165 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_045 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_045, fv_syn_cnnc] using (nb088_compact_fv_empty_0047 u A B R)

theorem nb088_wpp_notmem_0166 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_049 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_049, fv_syn_cnnc] using (nb088_compact_fv_empty_0048 A B C R)

theorem nb088_wpp_notmem_0167 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_050 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_050, fv_syn_cnnc] using (nb088_compact_fv_empty_0049 u A B R)

theorem nb088_wpp_notmem_0168 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_047 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_047, fv_syn_cnnc] using (nb088_compact_fv_empty_0050 A B C R)

theorem nb088_wpp_notmem_0169 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_048 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_048, fv_syn_cnnc] using (nb088_compact_fv_empty_0051 u A B R)

theorem nb088_wpp_notmem_0170 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_041 A B C R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_041, fv_syn_cnnc] using (nb088_compact_fv_empty_0052 A B C R)

theorem nb088_wpp_notmem_0171 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_042 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb088_alpha_dummy_042, fv_syn_cnnc] using (nb088_compact_fv_empty_0053 u A B R)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
