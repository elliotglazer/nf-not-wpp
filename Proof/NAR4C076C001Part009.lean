import NAR4C076C001Part008

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

noncomputable def nb076_split_alpha_0003 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TAlphaWff [((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_010)) (Class.cv (nb076_alpha_dummy_005))) (Wff.neg (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_012 g m n a b)) (Class.cv (nb076_alpha_dummy_006 g m n a b))) (Wff.neg (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0087 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0083) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0085 g m n a b) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) (by decide)) (freshVar_injective (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0061 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0060) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0061 g m n a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0091 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0089 g m n a b) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_010))).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0064) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0065 g m n a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0065 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0063 g m n a b) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060), (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059), (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053), (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054), (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079), (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (nb076_wpp_refl_0010 g m n a b))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0069 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0067 g m n a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0073 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0071 g m n a b) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0069 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0067 g m n a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0073 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0071 g m n a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060), (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059), (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053), (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054), (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079), (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (nb076_wpp_refl_0011 g m n a b))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0077 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0075 g m n a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0077 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0075 g m n a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0081 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0079 g m n a b) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0081 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0079 g m n a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0063 g m n a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053), (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054), (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079), (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (nb076_wpp_refl_0012 g m n a b))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0063 g m n a b) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0063 g m n a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053), (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054), (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079), (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (nb076_wpp_refl_0012 g m n a b)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0061 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0060) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0061 g m n a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0091 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0089 g m n a b) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_010))).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0064) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0065 g m n a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0065 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0063 g m n a b) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060), (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059), (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053), (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054), (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079), (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (nb076_wpp_refl_0010 g m n a b))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0069 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0067 g m n a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0073 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0071 g m n a b) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0069 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0067 g m n a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0073 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0071 g m n a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060), (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059), (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053), (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054), (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079), (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (nb076_wpp_refl_0011 g m n a b))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0077 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0075 g m n a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0077 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0075 g m n a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0081 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0079 g m n a b) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0081 g m n a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0079 g m n a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0063 g m n a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053), (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054), (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079), (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (nb076_wpp_refl_0012 g m n a b))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0063 g m n a b) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0063 g m n a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053), (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054), (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079), (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (nb076_wpp_refl_0012 g m n a b)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_ccompl (syn_csn (syn_c0c))) (nb076_wpp_refl_0013 g m n a b)))))))))))

theorem nb076_wpp_notmem_0198 : (nb076_alpha_dummy_005) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_005, fv_syn_cncs] using (nb076_compact_fv_empty_0028)

theorem nb076_wpp_notmem_0199 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_006, fv_syn_cncs] using (nb076_compact_fv_empty_0029 g m n a b)

theorem nb076_wpp_notmem_0200 : (nb076_alpha_dummy_004) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_004, fv_syn_cncs] using (nb076_compact_fv_empty_0030)

theorem nb076_wpp_notmem_0201 (n : Var) : n ∉ ((syn_cncs)).fv := by
  simpa only [fv_syn_cncs] using (nb076_compact_fv_empty_0031 n)

theorem nb076_wpp_notmem_0202 : (nb076_alpha_dummy_003) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_003, fv_syn_cncs] using (nb076_compact_fv_empty_0032)

theorem nb076_wpp_notmem_0203 (m : Var) : m ∉ ((syn_cncs)).fv := by
  simpa only [fv_syn_cncs] using (nb076_compact_fv_empty_0033 m)

theorem nb076_wpp_notmem_0204 : (nb076_alpha_dummy_007) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_007, fv_syn_cncs] using (nb076_compact_fv_empty_0034)

theorem nb076_wpp_notmem_0205 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_008 g m n a b) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_008, fv_syn_cncs] using (nb076_compact_fv_empty_0035 g m n a b)

theorem nb076_compact_envfresh_0014 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TEnvFresh [((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_cncs)).fv := by
  exact (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b) (nb076_wpp_notmem_0198) (nb076_wpp_notmem_0199 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0200) (nb076_wpp_notmem_0201 n) (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0202) (nb076_wpp_notmem_0203 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0204) (nb076_wpp_notmem_0205 g m n a b) (TEnvFresh.nil ((syn_cncs)).fv)))))

noncomputable def nb076_wpp_refl_0014 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TReflOn [((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_cncs)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0014 g m n a b)

theorem nb076_compact_fv_empty_0060 : (nb076_alpha_dummy_097) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0206 : (nb076_alpha_dummy_097) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_097, fv_syn_c1c] using (nb076_compact_fv_empty_0060)

theorem nb076_compact_fv_empty_0061 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_100 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0207 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_100 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_100, fv_syn_c1c] using (nb076_compact_fv_empty_0061 g a b)

theorem nb076_compact_fv_empty_0062 : (nb076_alpha_dummy_096) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0208 : (nb076_alpha_dummy_096) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_096, fv_syn_c1c] using (nb076_compact_fv_empty_0062)

theorem nb076_compact_fv_empty_0063 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_099 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0209 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_099 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_099, fv_syn_c1c] using (nb076_compact_fv_empty_0063 g a b)

theorem nb076_compact_fv_empty_0064 : (nb076_alpha_dummy_095) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0210 : (nb076_alpha_dummy_095) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_095, fv_syn_c1c] using (nb076_compact_fv_empty_0064)

theorem nb076_compact_fv_empty_0065 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_098 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0211 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_098 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_098, fv_syn_c1c] using (nb076_compact_fv_empty_0065 g a b)

theorem nb076_compact_fv_empty_0066 : (nb076_alpha_dummy_093) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0212 : (nb076_alpha_dummy_093) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_093, fv_syn_c1c] using (nb076_compact_fv_empty_0066)

theorem nb076_compact_fv_empty_0067 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_094 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0213 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_094 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_094, fv_syn_c1c] using (nb076_compact_fv_empty_0067 g a b)

theorem nb076_compact_fv_empty_0068 : (nb076_alpha_dummy_089) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0214 : (nb076_alpha_dummy_089) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_089, fv_syn_c1c] using (nb076_compact_fv_empty_0068)

theorem nb076_compact_fv_empty_0069 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_091 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0215 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_091 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_091, fv_syn_c1c] using (nb076_compact_fv_empty_0069 g a b)

theorem nb076_compact_fv_empty_0070 : (nb076_alpha_dummy_090) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0216 : (nb076_alpha_dummy_090) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_090, fv_syn_c1c] using (nb076_compact_fv_empty_0070)

theorem nb076_compact_fv_empty_0071 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_092 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0217 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_092 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_092, fv_syn_c1c] using (nb076_compact_fv_empty_0071 g a b)

theorem nb076_compact_fv_empty_0072 : (nb076_alpha_dummy_082) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0218 : (nb076_alpha_dummy_082) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_082, fv_syn_c1c] using (nb076_compact_fv_empty_0072)

theorem nb076_compact_fv_empty_0073 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_084 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0219 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_084 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_084, fv_syn_c1c] using (nb076_compact_fv_empty_0073 g a b)

theorem nb076_compact_fv_empty_0074 : (nb076_alpha_dummy_081) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0220 : (nb076_alpha_dummy_081) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_081, fv_syn_c1c] using (nb076_compact_fv_empty_0074)

theorem nb076_compact_fv_empty_0075 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_083 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0221 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_083 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_083, fv_syn_c1c] using (nb076_compact_fv_empty_0075 g a b)

theorem nb076_compact_fv_empty_0076 : (nb076_alpha_dummy_087) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0222 : (nb076_alpha_dummy_087) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_087, fv_syn_c1c] using (nb076_compact_fv_empty_0076)

theorem nb076_compact_fv_empty_0077 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_088 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0223 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_088 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_088, fv_syn_c1c] using (nb076_compact_fv_empty_0077 g a b)

theorem nb076_compact_fv_empty_0078 : (nb076_alpha_dummy_085) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0224 : (nb076_alpha_dummy_085) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_085, fv_syn_c1c] using (nb076_compact_fv_empty_0078)

theorem nb076_compact_fv_empty_0079 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_086 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0225 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_086 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_086, fv_syn_c1c] using (nb076_compact_fv_empty_0079 g a b)

theorem nb076_compact_fv_empty_0080 : (nb076_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0226 : (nb076_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_002, fv_syn_c1c] using (nb076_compact_fv_empty_0080)

theorem nb076_compact_fv_empty_0081 (g : Var) : g ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0227 (g : Var) : g ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb076_compact_fv_empty_0081 g)

theorem nb076_compact_fv_empty_0082 : (nb076_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0228 : (nb076_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_001, fv_syn_c1c] using (nb076_compact_fv_empty_0082)

theorem nb076_compact_fv_empty_0083 (b : Var) : b ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0229 (b : Var) : b ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb076_compact_fv_empty_0083 b)

theorem nb076_compact_fv_empty_0084 : (nb076_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0230 : (nb076_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_000, fv_syn_c1c] using (nb076_compact_fv_empty_0084)

theorem nb076_compact_fv_empty_0085 (a : Var) : a ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0231 (a : Var) : a ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb076_compact_fv_empty_0085 a)

theorem nb076_compact_envfresh_0015 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TEnvFresh [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096), (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095), (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb076_alpha_dummy_097) (nb076_alpha_dummy_100 g a b) (nb076_wpp_notmem_0206) (nb076_wpp_notmem_0207 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_096) (nb076_alpha_dummy_099 g a b) (nb076_wpp_notmem_0208) (nb076_wpp_notmem_0209 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_095) (nb076_alpha_dummy_098 g a b) (nb076_wpp_notmem_0210) (nb076_wpp_notmem_0211 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_093) (nb076_alpha_dummy_094 g a b) (nb076_wpp_notmem_0212) (nb076_wpp_notmem_0213 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_089) (nb076_alpha_dummy_091 g a b) (nb076_wpp_notmem_0214) (nb076_wpp_notmem_0215 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_090) (nb076_alpha_dummy_092 g a b) (nb076_wpp_notmem_0216) (nb076_wpp_notmem_0217 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_082) (nb076_alpha_dummy_084 g a b) (nb076_wpp_notmem_0218) (nb076_wpp_notmem_0219 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_081) (nb076_alpha_dummy_083 g a b) (nb076_wpp_notmem_0220) (nb076_wpp_notmem_0221 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_087) (nb076_alpha_dummy_088 g a b) (nb076_wpp_notmem_0222) (nb076_wpp_notmem_0223 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_085) (nb076_alpha_dummy_086 g a b) (nb076_wpp_notmem_0224) (nb076_wpp_notmem_0225 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_002) g (nb076_wpp_notmem_0226) (nb076_wpp_notmem_0227 g) (TEnvFresh.consFresh (nb076_alpha_dummy_001) b (nb076_wpp_notmem_0228) (nb076_wpp_notmem_0229 b) (TEnvFresh.consFresh (nb076_alpha_dummy_000) a (nb076_wpp_notmem_0230) (nb076_wpp_notmem_0231 a) (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b) (nb076_wpp_notmem_0028) (nb076_wpp_notmem_0029 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0030) (nb076_wpp_notmem_0031 n) (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0032) (nb076_wpp_notmem_0033 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0034) (nb076_wpp_notmem_0035 g m n a b) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb076_wpp_refl_0015 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TReflOn [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096), (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095), (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0015 g m n a b)

theorem nb076_wpp_notmem_0232 : (nb076_alpha_dummy_097) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_097, fv_syn_c0] using (nb076_compact_fv_empty_0060)

theorem nb076_wpp_notmem_0233 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_100 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_100, fv_syn_c0] using (nb076_compact_fv_empty_0061 g a b)

theorem nb076_wpp_notmem_0234 : (nb076_alpha_dummy_096) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_096, fv_syn_c0] using (nb076_compact_fv_empty_0062)

theorem nb076_wpp_notmem_0235 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_099 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_099, fv_syn_c0] using (nb076_compact_fv_empty_0063 g a b)

theorem nb076_wpp_notmem_0236 : (nb076_alpha_dummy_095) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_095, fv_syn_c0] using (nb076_compact_fv_empty_0064)

theorem nb076_wpp_notmem_0237 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_098 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_098, fv_syn_c0] using (nb076_compact_fv_empty_0065 g a b)

theorem nb076_wpp_notmem_0238 : (nb076_alpha_dummy_093) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_093, fv_syn_c0] using (nb076_compact_fv_empty_0066)

theorem nb076_wpp_notmem_0239 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_094 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_094, fv_syn_c0] using (nb076_compact_fv_empty_0067 g a b)

theorem nb076_wpp_notmem_0240 : (nb076_alpha_dummy_089) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_089, fv_syn_c0] using (nb076_compact_fv_empty_0068)

theorem nb076_wpp_notmem_0241 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_091 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_091, fv_syn_c0] using (nb076_compact_fv_empty_0069 g a b)

theorem nb076_wpp_notmem_0242 : (nb076_alpha_dummy_090) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_090, fv_syn_c0] using (nb076_compact_fv_empty_0070)

theorem nb076_wpp_notmem_0243 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_092 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_092, fv_syn_c0] using (nb076_compact_fv_empty_0071 g a b)

theorem nb076_wpp_notmem_0244 : (nb076_alpha_dummy_082) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_082, fv_syn_c0] using (nb076_compact_fv_empty_0072)

theorem nb076_wpp_notmem_0245 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_084 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_084, fv_syn_c0] using (nb076_compact_fv_empty_0073 g a b)

theorem nb076_wpp_notmem_0246 : (nb076_alpha_dummy_081) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_081, fv_syn_c0] using (nb076_compact_fv_empty_0074)

theorem nb076_wpp_notmem_0247 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_083 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_083, fv_syn_c0] using (nb076_compact_fv_empty_0075 g a b)

theorem nb076_wpp_notmem_0248 : (nb076_alpha_dummy_087) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_087, fv_syn_c0] using (nb076_compact_fv_empty_0076)

theorem nb076_wpp_notmem_0249 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_088 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_088, fv_syn_c0] using (nb076_compact_fv_empty_0077 g a b)

theorem nb076_wpp_notmem_0250 : (nb076_alpha_dummy_085) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_085, fv_syn_c0] using (nb076_compact_fv_empty_0078)

theorem nb076_wpp_notmem_0251 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_086 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_086, fv_syn_c0] using (nb076_compact_fv_empty_0079 g a b)

theorem nb076_wpp_notmem_0252 : (nb076_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_002, fv_syn_c0] using (nb076_compact_fv_empty_0080)

theorem nb076_wpp_notmem_0253 (g : Var) : g ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb076_compact_fv_empty_0081 g)

theorem nb076_wpp_notmem_0254 : (nb076_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_001, fv_syn_c0] using (nb076_compact_fv_empty_0082)

theorem nb076_wpp_notmem_0255 (b : Var) : b ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb076_compact_fv_empty_0083 b)

theorem nb076_wpp_notmem_0256 : (nb076_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_000, fv_syn_c0] using (nb076_compact_fv_empty_0084)

theorem nb076_wpp_notmem_0257 (a : Var) : a ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb076_compact_fv_empty_0085 a)

theorem nb076_compact_envfresh_0016 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TEnvFresh [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096), (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095), (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb076_alpha_dummy_097) (nb076_alpha_dummy_100 g a b) (nb076_wpp_notmem_0232) (nb076_wpp_notmem_0233 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_096) (nb076_alpha_dummy_099 g a b) (nb076_wpp_notmem_0234) (nb076_wpp_notmem_0235 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_095) (nb076_alpha_dummy_098 g a b) (nb076_wpp_notmem_0236) (nb076_wpp_notmem_0237 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_093) (nb076_alpha_dummy_094 g a b) (nb076_wpp_notmem_0238) (nb076_wpp_notmem_0239 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_089) (nb076_alpha_dummy_091 g a b) (nb076_wpp_notmem_0240) (nb076_wpp_notmem_0241 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_090) (nb076_alpha_dummy_092 g a b) (nb076_wpp_notmem_0242) (nb076_wpp_notmem_0243 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_082) (nb076_alpha_dummy_084 g a b) (nb076_wpp_notmem_0244) (nb076_wpp_notmem_0245 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_081) (nb076_alpha_dummy_083 g a b) (nb076_wpp_notmem_0246) (nb076_wpp_notmem_0247 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_087) (nb076_alpha_dummy_088 g a b) (nb076_wpp_notmem_0248) (nb076_wpp_notmem_0249 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_085) (nb076_alpha_dummy_086 g a b) (nb076_wpp_notmem_0250) (nb076_wpp_notmem_0251 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_002) g (nb076_wpp_notmem_0252) (nb076_wpp_notmem_0253 g) (TEnvFresh.consFresh (nb076_alpha_dummy_001) b (nb076_wpp_notmem_0254) (nb076_wpp_notmem_0255 b) (TEnvFresh.consFresh (nb076_alpha_dummy_000) a (nb076_wpp_notmem_0256) (nb076_wpp_notmem_0257 a) (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b) (nb076_wpp_notmem_0064) (nb076_wpp_notmem_0065 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0066) (nb076_wpp_notmem_0067 n) (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0068) (nb076_wpp_notmem_0069 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0070) (nb076_wpp_notmem_0071 g m n a b) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb076_wpp_refl_0016 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TReflOn [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096), (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095), (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0016 g m n a b)

theorem nb076_wpp_notmem_0258 : (nb076_alpha_dummy_093) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_093, fv_syn_cnnc] using (nb076_compact_fv_empty_0066)

theorem nb076_wpp_notmem_0259 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_094 g a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_094, fv_syn_cnnc] using (nb076_compact_fv_empty_0067 g a b)

theorem nb076_wpp_notmem_0260 : (nb076_alpha_dummy_089) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_089, fv_syn_cnnc] using (nb076_compact_fv_empty_0068)

theorem nb076_wpp_notmem_0261 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_091 g a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_091, fv_syn_cnnc] using (nb076_compact_fv_empty_0069 g a b)

theorem nb076_wpp_notmem_0262 : (nb076_alpha_dummy_090) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_090, fv_syn_cnnc] using (nb076_compact_fv_empty_0070)

theorem nb076_wpp_notmem_0263 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_092 g a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_092, fv_syn_cnnc] using (nb076_compact_fv_empty_0071 g a b)

theorem nb076_wpp_notmem_0264 : (nb076_alpha_dummy_082) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_082, fv_syn_cnnc] using (nb076_compact_fv_empty_0072)

theorem nb076_wpp_notmem_0265 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_084 g a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_084, fv_syn_cnnc] using (nb076_compact_fv_empty_0073 g a b)

theorem nb076_wpp_notmem_0266 : (nb076_alpha_dummy_081) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_081, fv_syn_cnnc] using (nb076_compact_fv_empty_0074)

theorem nb076_wpp_notmem_0267 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_083 g a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_083, fv_syn_cnnc] using (nb076_compact_fv_empty_0075 g a b)

theorem nb076_wpp_notmem_0268 : (nb076_alpha_dummy_087) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_087, fv_syn_cnnc] using (nb076_compact_fv_empty_0076)

theorem nb076_wpp_notmem_0269 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_088 g a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_088, fv_syn_cnnc] using (nb076_compact_fv_empty_0077 g a b)

theorem nb076_wpp_notmem_0270 : (nb076_alpha_dummy_085) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_085, fv_syn_cnnc] using (nb076_compact_fv_empty_0078)

theorem nb076_wpp_notmem_0271 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_086 g a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_086, fv_syn_cnnc] using (nb076_compact_fv_empty_0079 g a b)

theorem nb076_wpp_notmem_0272 : (nb076_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_002, fv_syn_cnnc] using (nb076_compact_fv_empty_0080)

theorem nb076_wpp_notmem_0273 (g : Var) : g ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb076_compact_fv_empty_0081 g)

theorem nb076_wpp_notmem_0274 : (nb076_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_001, fv_syn_cnnc] using (nb076_compact_fv_empty_0082)

theorem nb076_wpp_notmem_0275 (b : Var) : b ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb076_compact_fv_empty_0083 b)

theorem nb076_wpp_notmem_0276 : (nb076_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_000, fv_syn_cnnc] using (nb076_compact_fv_empty_0084)

theorem nb076_wpp_notmem_0277 (a : Var) : a ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb076_compact_fv_empty_0085 a)

theorem nb076_compact_envfresh_0017 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TEnvFresh [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb076_alpha_dummy_093) (nb076_alpha_dummy_094 g a b) (nb076_wpp_notmem_0258) (nb076_wpp_notmem_0259 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_089) (nb076_alpha_dummy_091 g a b) (nb076_wpp_notmem_0260) (nb076_wpp_notmem_0261 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_090) (nb076_alpha_dummy_092 g a b) (nb076_wpp_notmem_0262) (nb076_wpp_notmem_0263 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_082) (nb076_alpha_dummy_084 g a b) (nb076_wpp_notmem_0264) (nb076_wpp_notmem_0265 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_081) (nb076_alpha_dummy_083 g a b) (nb076_wpp_notmem_0266) (nb076_wpp_notmem_0267 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_087) (nb076_alpha_dummy_088 g a b) (nb076_wpp_notmem_0268) (nb076_wpp_notmem_0269 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_085) (nb076_alpha_dummy_086 g a b) (nb076_wpp_notmem_0270) (nb076_wpp_notmem_0271 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_002) g (nb076_wpp_notmem_0272) (nb076_wpp_notmem_0273 g) (TEnvFresh.consFresh (nb076_alpha_dummy_001) b (nb076_wpp_notmem_0274) (nb076_wpp_notmem_0275 b) (TEnvFresh.consFresh (nb076_alpha_dummy_000) a (nb076_wpp_notmem_0276) (nb076_wpp_notmem_0277 a) (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b) (nb076_wpp_notmem_0094) (nb076_wpp_notmem_0095 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0096) (nb076_wpp_notmem_0097 n) (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0098) (nb076_wpp_notmem_0099 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0100) (nb076_wpp_notmem_0101 g m n a b) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb076_wpp_refl_0017 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TReflOn [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0017 g m n a b)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
