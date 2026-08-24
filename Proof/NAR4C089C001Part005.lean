import NAR4C089C001Part004

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

noncomputable def nb089_split_alpha_0001 (u : Var) (A : Class) (B : Class) (R : Class) : TAlphaWff [((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_011 A B R)) (syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))) (Wff.neg (Wff.classMem (Class.cv (nb089_alpha_dummy_011 A B R)) (syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c)))))))))) (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_012 u A B R)) (syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))) (Wff.neg (Wff.classMem (Class.cv (nb089_alpha_dummy_012 u A B R)) (syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0010 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0011 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0007 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0009 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0004 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0005 u A B R) 0)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0012 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0013 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0012 A B R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0013 u A B R) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0016 A B R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0017 u A B R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0016 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0017 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0014 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0015 u A B R) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (nb089_wpp_refl_0000 u A B R))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0020 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0021 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0018 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0019 u A B R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0024 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0025 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0022 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0023 u A B R) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0020 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0021 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0018 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0019 u A B R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0024 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0025 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0022 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0023 u A B R) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] (syn_c0) (nb089_wpp_refl_0001 u A B R))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0028 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0029 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0026 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0027 u A B R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0028 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0029 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0026 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0027 u A B R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0032 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0033 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0030 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0031 u A B R) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0032 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0033 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0030 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0031 u A B R) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0014 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0015 u A B R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (nb089_wpp_refl_0002 u A B R))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0014 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0015 u A B R) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0014 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0015 u A B R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (nb089_wpp_refl_0002 u A B R)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0010 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0011 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0007 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0009 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0004 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0005 u A B R) 0)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0012 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0013 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0012 A B R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0013 u A B R) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0016 A B R) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0017 u A B R) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0016 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0017 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0014 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0015 u A B R) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (nb089_wpp_refl_0000 u A B R))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0020 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0021 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0018 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0019 u A B R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0024 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0025 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0022 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0023 u A B R) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0020 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0021 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0018 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0019 u A B R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0024 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0025 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0022 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0023 u A B R) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)), ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)), ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)), ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] (syn_c0) (nb089_wpp_refl_0001 u A B R))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0028 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0029 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0026 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0027 u A B R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0028 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0029 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0026 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0027 u A B R) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0032 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0033 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0030 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0031 u A B R) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0032 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0033 u A B R) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0030 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0031 u A B R) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0014 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0015 u A B R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (nb089_wpp_refl_0002 u A B R))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0014 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0015 u A B R) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0014 A B R) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0015 u A B R) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)), ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)), ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)), ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)), ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)), ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)), ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (nb089_wpp_refl_0002 u A B R)))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb089_split_alpha_0000 u A B R))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb089_split_alpha_0000 u A B R)))))))))))))))

theorem nb089_focused_notmem_0000 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∉ A.fv := by
  change freshVar (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 (syn_cuni A))).symm ▸ (((fv_syn_cpw1 (syn_cuni A)).symm ▸ (((fv_syn_cuni A).symm ▸ (hu)))))))))

theorem nb089_wpp_notmem_0114 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_003, fv_syn_cpw1, fv_syn_cuni] using (nb089_focused_notmem_0000 A B R)

theorem nb089_focused_notmem_0001 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∉ A.fv := by
  change freshVar (({u} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv u))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 (syn_cuni A))).symm ▸ (((fv_syn_cpw1 (syn_cuni A)).symm ▸ (((fv_syn_cuni A).symm ▸ (hu)))))))))

theorem nb089_wpp_notmem_0115 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_004, fv_syn_cpw1, fv_syn_cuni] using (nb089_focused_notmem_0001 u A B R)

theorem nb089_focused_notmem_0002 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∉ A.fv := by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb089_wpp_notmem_0116 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_000, fv_syn_cpw1, fv_syn_cuni] using (nb089_focused_notmem_0002 A B R)

theorem nb089_wpp_notmem_0117 (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) : u ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [fv_syn_cpw1, fv_syn_cuni] using dv_A_u

theorem nb089_focused_notmem_0003 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_005 A B R) ∉ A.fv := by
  change freshVar (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R)) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R)) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 (syn_cuni A))).symm ▸ (((fv_syn_cpw1 (syn_cuni A)).symm ▸ (((fv_syn_cuni A).symm ▸ (hu))))))))))))))

theorem nb089_wpp_notmem_0118 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_005 A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_005, fv_syn_cpw1, fv_syn_cuni] using (nb089_focused_notmem_0003 A B R)

theorem nb089_focused_notmem_0004 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_006 u A B R) ∉ A.fv := by
  change freshVar (({u} : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R)) (syn_cfdrowfib R A B (Class.cv u)))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A)))).symm ▸ (Finset.mem_union_right _ (((fv_syn_cpw1 (syn_cpw1 (syn_cuni A))).symm ▸ (((fv_syn_cpw1 (syn_cuni A)).symm ▸ (((fv_syn_cuni A).symm ▸ (hu))))))))))))))

theorem nb089_wpp_notmem_0119 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_006 u A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_006, fv_syn_cpw1, fv_syn_cuni] using (nb089_focused_notmem_0004 u A B R)

theorem nb089_focused_notmem_0005 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_001 A B R) ∉ A.fv := by
  change freshVar (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪ ((syn_c0)).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_left _ (((fv_syn_wbr R (syn_cwe) A).symm ▸ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))))))

theorem nb089_wpp_notmem_0120 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_001 A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_001, fv_syn_cpw1, fv_syn_cuni] using (nb089_focused_notmem_0005 A B R)

theorem nb089_focused_notmem_0006 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_002 u A B R) ∉ A.fv := by
  change freshVar (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_left _ (((fv_syn_wbr R (syn_cwe) A).symm ▸ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))))))

theorem nb089_wpp_notmem_0121 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_002 u A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_002, fv_syn_cpw1, fv_syn_cuni] using (nb089_focused_notmem_0006 u A B R)

theorem nb089_compact_envfresh_0007 (u : Var) (A : Class) (B : Class) (R : Class) (dv_A_u : u ∉ A.fv) : TEnvFresh [((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  exact (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R) (nb089_wpp_notmem_0114 A B R) (nb089_wpp_notmem_0115 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0116 A B R) (nb089_wpp_notmem_0117 u A dv_A_u) (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0118 A B R) (nb089_wpp_notmem_0119 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0120 A B R) (nb089_wpp_notmem_0121 u A B R) (TEnvFresh.nil ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv)))))

noncomputable def nb089_wpp_refl_0007 (u : Var) (A : Class) (B : Class) (R : Class) (dv_A_u : u ∉ A.fv) : TReflOn [((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0007 u A B R dv_A_u)

theorem nb089_compact_fv_empty_0034 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_063 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0122 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_063 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_063, fv_syn_c1c] using (nb089_compact_fv_empty_0034 A B R)

theorem nb089_compact_fv_empty_0035 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_066 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0123 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_066 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_066, fv_syn_c1c] using (nb089_compact_fv_empty_0035 u A B R)

theorem nb089_compact_fv_empty_0036 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_062 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0124 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_062 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_062, fv_syn_c1c] using (nb089_compact_fv_empty_0036 A B R)

theorem nb089_compact_fv_empty_0037 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_065 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0125 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_065 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_065, fv_syn_c1c] using (nb089_compact_fv_empty_0037 u A B R)

theorem nb089_compact_fv_empty_0038 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_061 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0126 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_061 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_061, fv_syn_c1c] using (nb089_compact_fv_empty_0038 A B R)

theorem nb089_compact_fv_empty_0039 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_064 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0127 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_064 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_064, fv_syn_c1c] using (nb089_compact_fv_empty_0039 u A B R)

theorem nb089_compact_fv_empty_0040 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_059 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0128 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_059 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_059, fv_syn_c1c] using (nb089_compact_fv_empty_0040 A B R)

theorem nb089_compact_fv_empty_0041 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_060 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0129 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_060 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_060, fv_syn_c1c] using (nb089_compact_fv_empty_0041 u A B R)

theorem nb089_compact_fv_empty_0042 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_055 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0130 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_055 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_055, fv_syn_c1c] using (nb089_compact_fv_empty_0042 A B R)

theorem nb089_compact_fv_empty_0043 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_057 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0131 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_057 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_057, fv_syn_c1c] using (nb089_compact_fv_empty_0043 u A B R)

theorem nb089_compact_fv_empty_0044 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_056 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0132 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_056 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_056, fv_syn_c1c] using (nb089_compact_fv_empty_0044 A B R)

theorem nb089_compact_fv_empty_0045 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_058 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0133 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_058 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_058, fv_syn_c1c] using (nb089_compact_fv_empty_0045 u A B R)

theorem nb089_compact_fv_empty_0046 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_046 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0134 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_046 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_046, fv_syn_c1c] using (nb089_compact_fv_empty_0046 A B R)

theorem nb089_compact_fv_empty_0047 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_048 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0135 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_048 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_048, fv_syn_c1c] using (nb089_compact_fv_empty_0047 u A B R)

theorem nb089_compact_fv_empty_0048 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_045 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0136 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_045 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_045, fv_syn_c1c] using (nb089_compact_fv_empty_0048 A B R)

theorem nb089_compact_fv_empty_0049 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_047 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0137 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_047 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_047, fv_syn_c1c] using (nb089_compact_fv_empty_0049 u A B R)

theorem nb089_compact_fv_empty_0050 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_051 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0138 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_051 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_051, fv_syn_c1c] using (nb089_compact_fv_empty_0050 A B R)

theorem nb089_compact_fv_empty_0051 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_052 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0139 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_052 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_052, fv_syn_c1c] using (nb089_compact_fv_empty_0051 u A B R)

theorem nb089_compact_fv_empty_0052 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_049 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0140 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_049 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_049, fv_syn_c1c] using (nb089_compact_fv_empty_0052 A B R)

theorem nb089_compact_fv_empty_0053 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_050 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0141 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_050 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_050, fv_syn_c1c] using (nb089_compact_fv_empty_0053 u A B R)

theorem nb089_compact_fv_empty_0054 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_043 A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0142 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_043 A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_043, fv_syn_c1c] using (nb089_compact_fv_empty_0054 A B R)

theorem nb089_compact_fv_empty_0055 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_044 u A B R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb089_wpp_notmem_0143 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_044 u A B R) ∉ ((syn_c1c)).fv := by
  simpa only [nb089_alpha_dummy_044, fv_syn_c1c] using (nb089_compact_fv_empty_0055 u A B R)

theorem nb089_compact_envfresh_0008 (u : Var) (A : Class) (B : Class) (R : Class) : TEnvFresh [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)), ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)), ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)), ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)), ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)), ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)), ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)), ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)), ((nb089_alpha_dummy_051 A B R), (nb089_alpha_dummy_052 u A B R)), ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)), ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb089_alpha_dummy_063 A B R) (nb089_alpha_dummy_066 u A B R) (nb089_wpp_notmem_0122 A B R) (nb089_wpp_notmem_0123 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_062 A B R) (nb089_alpha_dummy_065 u A B R) (nb089_wpp_notmem_0124 A B R) (nb089_wpp_notmem_0125 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_061 A B R) (nb089_alpha_dummy_064 u A B R) (nb089_wpp_notmem_0126 A B R) (nb089_wpp_notmem_0127 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_059 A B R) (nb089_alpha_dummy_060 u A B R) (nb089_wpp_notmem_0128 A B R) (nb089_wpp_notmem_0129 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_055 A B R) (nb089_alpha_dummy_057 u A B R) (nb089_wpp_notmem_0130 A B R) (nb089_wpp_notmem_0131 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_056 A B R) (nb089_alpha_dummy_058 u A B R) (nb089_wpp_notmem_0132 A B R) (nb089_wpp_notmem_0133 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_046 A B R) (nb089_alpha_dummy_048 u A B R) (nb089_wpp_notmem_0134 A B R) (nb089_wpp_notmem_0135 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_045 A B R) (nb089_alpha_dummy_047 u A B R) (nb089_wpp_notmem_0136 A B R) (nb089_wpp_notmem_0137 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_051 A B R) (nb089_alpha_dummy_052 u A B R) (nb089_wpp_notmem_0138 A B R) (nb089_wpp_notmem_0139 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_049 A B R) (nb089_alpha_dummy_050 u A B R) (nb089_wpp_notmem_0140 A B R) (nb089_wpp_notmem_0141 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_043 A B R) (nb089_alpha_dummy_044 u A B R) (nb089_wpp_notmem_0142 A B R) (nb089_wpp_notmem_0143 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R) (nb089_wpp_notmem_0020 A B R) (nb089_wpp_notmem_0021 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0022 A B R) (nb089_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0024 A B R) (nb089_wpp_notmem_0025 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0026 A B R) (nb089_wpp_notmem_0027 u A B R) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb089_wpp_refl_0008 (u : Var) (A : Class) (B : Class) (R : Class) : TReflOn [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)), ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)), ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)), ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)), ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)), ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)), ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)), ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)), ((nb089_alpha_dummy_051 A B R), (nb089_alpha_dummy_052 u A B R)), ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)), ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0008 u A B R)

theorem nb089_wpp_notmem_0144 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_063 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_063, fv_syn_c0] using (nb089_compact_fv_empty_0034 A B R)

theorem nb089_wpp_notmem_0145 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_066 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_066, fv_syn_c0] using (nb089_compact_fv_empty_0035 u A B R)

theorem nb089_wpp_notmem_0146 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_062 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_062, fv_syn_c0] using (nb089_compact_fv_empty_0036 A B R)

theorem nb089_wpp_notmem_0147 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_065 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_065, fv_syn_c0] using (nb089_compact_fv_empty_0037 u A B R)

theorem nb089_wpp_notmem_0148 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_061 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_061, fv_syn_c0] using (nb089_compact_fv_empty_0038 A B R)

theorem nb089_wpp_notmem_0149 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_064 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_064, fv_syn_c0] using (nb089_compact_fv_empty_0039 u A B R)

theorem nb089_wpp_notmem_0150 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_059 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_059, fv_syn_c0] using (nb089_compact_fv_empty_0040 A B R)

theorem nb089_wpp_notmem_0151 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_060 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_060, fv_syn_c0] using (nb089_compact_fv_empty_0041 u A B R)

theorem nb089_wpp_notmem_0152 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_055 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_055, fv_syn_c0] using (nb089_compact_fv_empty_0042 A B R)

theorem nb089_wpp_notmem_0153 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_057 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_057, fv_syn_c0] using (nb089_compact_fv_empty_0043 u A B R)

theorem nb089_wpp_notmem_0154 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_056 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_056, fv_syn_c0] using (nb089_compact_fv_empty_0044 A B R)

theorem nb089_wpp_notmem_0155 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_058 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_058, fv_syn_c0] using (nb089_compact_fv_empty_0045 u A B R)

theorem nb089_wpp_notmem_0156 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_046 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_046, fv_syn_c0] using (nb089_compact_fv_empty_0046 A B R)

theorem nb089_wpp_notmem_0157 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_048 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_048, fv_syn_c0] using (nb089_compact_fv_empty_0047 u A B R)

theorem nb089_wpp_notmem_0158 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_045 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_045, fv_syn_c0] using (nb089_compact_fv_empty_0048 A B R)

theorem nb089_wpp_notmem_0159 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_047 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_047, fv_syn_c0] using (nb089_compact_fv_empty_0049 u A B R)

theorem nb089_wpp_notmem_0160 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_051 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_051, fv_syn_c0] using (nb089_compact_fv_empty_0050 A B R)

theorem nb089_wpp_notmem_0161 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_052 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_052, fv_syn_c0] using (nb089_compact_fv_empty_0051 u A B R)

theorem nb089_wpp_notmem_0162 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_049 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_049, fv_syn_c0] using (nb089_compact_fv_empty_0052 A B R)

theorem nb089_wpp_notmem_0163 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_050 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_050, fv_syn_c0] using (nb089_compact_fv_empty_0053 u A B R)

theorem nb089_wpp_notmem_0164 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_043 A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_043, fv_syn_c0] using (nb089_compact_fv_empty_0054 A B R)

theorem nb089_wpp_notmem_0165 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_044 u A B R) ∉ ((syn_c0)).fv := by
  simpa only [nb089_alpha_dummy_044, fv_syn_c0] using (nb089_compact_fv_empty_0055 u A B R)

theorem nb089_compact_envfresh_0009 (u : Var) (A : Class) (B : Class) (R : Class) : TEnvFresh [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)), ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)), ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)), ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)), ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)), ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)), ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)), ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)), ((nb089_alpha_dummy_051 A B R), (nb089_alpha_dummy_052 u A B R)), ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)), ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb089_alpha_dummy_063 A B R) (nb089_alpha_dummy_066 u A B R) (nb089_wpp_notmem_0144 A B R) (nb089_wpp_notmem_0145 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_062 A B R) (nb089_alpha_dummy_065 u A B R) (nb089_wpp_notmem_0146 A B R) (nb089_wpp_notmem_0147 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_061 A B R) (nb089_alpha_dummy_064 u A B R) (nb089_wpp_notmem_0148 A B R) (nb089_wpp_notmem_0149 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_059 A B R) (nb089_alpha_dummy_060 u A B R) (nb089_wpp_notmem_0150 A B R) (nb089_wpp_notmem_0151 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_055 A B R) (nb089_alpha_dummy_057 u A B R) (nb089_wpp_notmem_0152 A B R) (nb089_wpp_notmem_0153 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_056 A B R) (nb089_alpha_dummy_058 u A B R) (nb089_wpp_notmem_0154 A B R) (nb089_wpp_notmem_0155 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_046 A B R) (nb089_alpha_dummy_048 u A B R) (nb089_wpp_notmem_0156 A B R) (nb089_wpp_notmem_0157 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_045 A B R) (nb089_alpha_dummy_047 u A B R) (nb089_wpp_notmem_0158 A B R) (nb089_wpp_notmem_0159 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_051 A B R) (nb089_alpha_dummy_052 u A B R) (nb089_wpp_notmem_0160 A B R) (nb089_wpp_notmem_0161 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_049 A B R) (nb089_alpha_dummy_050 u A B R) (nb089_wpp_notmem_0162 A B R) (nb089_wpp_notmem_0163 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_043 A B R) (nb089_alpha_dummy_044 u A B R) (nb089_wpp_notmem_0164 A B R) (nb089_wpp_notmem_0165 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R) (nb089_wpp_notmem_0048 A B R) (nb089_wpp_notmem_0049 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0050 A B R) (nb089_wpp_notmem_0051 u) (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0052 A B R) (nb089_wpp_notmem_0053 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0054 A B R) (nb089_wpp_notmem_0055 u A B R) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb089_wpp_refl_0009 (u : Var) (A : Class) (B : Class) (R : Class) : TReflOn [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)), ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)), ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)), ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)), ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)), ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)), ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)), ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)), ((nb089_alpha_dummy_051 A B R), (nb089_alpha_dummy_052 u A B R)), ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)), ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)), ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)), ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0009 u A B R)

theorem nb089_wpp_notmem_0166 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_059 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_059, fv_syn_cnnc] using (nb089_compact_fv_empty_0040 A B R)

theorem nb089_wpp_notmem_0167 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_060 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_060, fv_syn_cnnc] using (nb089_compact_fv_empty_0041 u A B R)

theorem nb089_wpp_notmem_0168 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_055 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_055, fv_syn_cnnc] using (nb089_compact_fv_empty_0042 A B R)

theorem nb089_wpp_notmem_0169 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_057 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_057, fv_syn_cnnc] using (nb089_compact_fv_empty_0043 u A B R)

theorem nb089_wpp_notmem_0170 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_056 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_056, fv_syn_cnnc] using (nb089_compact_fv_empty_0044 A B R)

theorem nb089_wpp_notmem_0171 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_058 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_058, fv_syn_cnnc] using (nb089_compact_fv_empty_0045 u A B R)

theorem nb089_wpp_notmem_0172 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_046 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_046, fv_syn_cnnc] using (nb089_compact_fv_empty_0046 A B R)

theorem nb089_wpp_notmem_0173 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_048 u A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_048, fv_syn_cnnc] using (nb089_compact_fv_empty_0047 u A B R)

theorem nb089_wpp_notmem_0174 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_045 A B R) ∉ ((syn_cnnc)).fv := by
  simpa only [nb089_alpha_dummy_045, fv_syn_cnnc] using (nb089_compact_fv_empty_0048 A B R)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
