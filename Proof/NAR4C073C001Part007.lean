import NAR4C073C001Part006

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

noncomputable def nb073_split_alpha_0003 (x : Var) (y : Var) : TAlphaWff [((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_007)) (Class.cv (nb073_alpha_dummy_002))) (Wff.neg (Wff.classEq (Class.cv (nb073_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007))) (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_009 x y)) (Class.cv (nb073_alpha_dummy_003 x y))) (Wff.neg (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0087 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0083) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0085 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪ ((Class.cv (nb073_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb073_alpha_dummy_003 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0060) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0061 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0091 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0089 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_007))).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_009 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0064) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0065 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_058), (nb073_alpha_dummy_061 x y)), ((nb073_alpha_dummy_057), (nb073_alpha_dummy_060 x y)), ((nb073_alpha_dummy_056), (nb073_alpha_dummy_059 x y)), ((nb073_alpha_dummy_054), (nb073_alpha_dummy_055 x y)), ((nb073_alpha_dummy_050), (nb073_alpha_dummy_052 x y)), ((nb073_alpha_dummy_051), (nb073_alpha_dummy_053 x y)), ((nb073_alpha_dummy_076), (nb073_alpha_dummy_077 x y)), ((nb073_alpha_dummy_074), (nb073_alpha_dummy_075 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_c1c) (nb073_wpp_refl_0010 x y))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0067 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0073 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0071 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0067 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0073 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0071 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_058), (nb073_alpha_dummy_061 x y)), ((nb073_alpha_dummy_057), (nb073_alpha_dummy_060 x y)), ((nb073_alpha_dummy_056), (nb073_alpha_dummy_059 x y)), ((nb073_alpha_dummy_054), (nb073_alpha_dummy_055 x y)), ((nb073_alpha_dummy_050), (nb073_alpha_dummy_052 x y)), ((nb073_alpha_dummy_051), (nb073_alpha_dummy_053 x y)), ((nb073_alpha_dummy_076), (nb073_alpha_dummy_077 x y)), ((nb073_alpha_dummy_074), (nb073_alpha_dummy_075 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_c0) (nb073_wpp_refl_0011 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0077 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0075 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0077 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0075 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0081 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0079 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0081 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0079 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_054), (nb073_alpha_dummy_055 x y)), ((nb073_alpha_dummy_050), (nb073_alpha_dummy_052 x y)), ((nb073_alpha_dummy_051), (nb073_alpha_dummy_053 x y)), ((nb073_alpha_dummy_076), (nb073_alpha_dummy_077 x y)), ((nb073_alpha_dummy_074), (nb073_alpha_dummy_075 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_cnnc) (nb073_wpp_refl_0012 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_054), (nb073_alpha_dummy_055 x y)), ((nb073_alpha_dummy_050), (nb073_alpha_dummy_052 x y)), ((nb073_alpha_dummy_051), (nb073_alpha_dummy_053 x y)), ((nb073_alpha_dummy_076), (nb073_alpha_dummy_077 x y)), ((nb073_alpha_dummy_074), (nb073_alpha_dummy_075 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_cnnc) (nb073_wpp_refl_0012 x y)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0060) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0061 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0091 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0089 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_007))).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_009 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0064) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0065 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_058), (nb073_alpha_dummy_061 x y)), ((nb073_alpha_dummy_057), (nb073_alpha_dummy_060 x y)), ((nb073_alpha_dummy_056), (nb073_alpha_dummy_059 x y)), ((nb073_alpha_dummy_054), (nb073_alpha_dummy_055 x y)), ((nb073_alpha_dummy_050), (nb073_alpha_dummy_052 x y)), ((nb073_alpha_dummy_051), (nb073_alpha_dummy_053 x y)), ((nb073_alpha_dummy_076), (nb073_alpha_dummy_077 x y)), ((nb073_alpha_dummy_074), (nb073_alpha_dummy_075 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_c1c) (nb073_wpp_refl_0010 x y))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0067 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0073 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0071 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0067 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0073 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0071 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_058), (nb073_alpha_dummy_061 x y)), ((nb073_alpha_dummy_057), (nb073_alpha_dummy_060 x y)), ((nb073_alpha_dummy_056), (nb073_alpha_dummy_059 x y)), ((nb073_alpha_dummy_054), (nb073_alpha_dummy_055 x y)), ((nb073_alpha_dummy_050), (nb073_alpha_dummy_052 x y)), ((nb073_alpha_dummy_051), (nb073_alpha_dummy_053 x y)), ((nb073_alpha_dummy_076), (nb073_alpha_dummy_077 x y)), ((nb073_alpha_dummy_074), (nb073_alpha_dummy_075 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_c0) (nb073_wpp_refl_0011 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0077 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0075 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0077 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0075 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0081 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0079 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0081 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0079 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_054), (nb073_alpha_dummy_055 x y)), ((nb073_alpha_dummy_050), (nb073_alpha_dummy_052 x y)), ((nb073_alpha_dummy_051), (nb073_alpha_dummy_053 x y)), ((nb073_alpha_dummy_076), (nb073_alpha_dummy_077 x y)), ((nb073_alpha_dummy_074), (nb073_alpha_dummy_075 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_cnnc) (nb073_wpp_refl_0012 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_054), (nb073_alpha_dummy_055 x y)), ((nb073_alpha_dummy_050), (nb073_alpha_dummy_052 x y)), ((nb073_alpha_dummy_051), (nb073_alpha_dummy_053 x y)), ((nb073_alpha_dummy_076), (nb073_alpha_dummy_077 x y)), ((nb073_alpha_dummy_074), (nb073_alpha_dummy_075 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_cnnc) (nb073_wpp_refl_0012 x y)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb073_alpha_dummy_074), (nb073_alpha_dummy_075 x y)), ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_072), (nb073_alpha_dummy_073 x y)), ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] (syn_ccompl (syn_csn (syn_c0c))) (nb073_wpp_refl_0013 x y)))))))))))

theorem nb073_wpp_notmem_0198 : (nb073_alpha_dummy_002) ∉ ((syn_cvv)).fv := by
  simpa only [nb073_alpha_dummy_002, fv_syn_cvv] using (nb073_compact_fv_empty_0028)

theorem nb073_wpp_notmem_0199 (x : Var) (y : Var) : (nb073_alpha_dummy_003 x y) ∉ ((syn_cvv)).fv := by
  simpa only [nb073_alpha_dummy_003, fv_syn_cvv] using (nb073_compact_fv_empty_0029 x y)

theorem nb073_wpp_notmem_0200 : (nb073_alpha_dummy_001) ∉ ((syn_cvv)).fv := by
  simpa only [nb073_alpha_dummy_001, fv_syn_cvv] using (nb073_compact_fv_empty_0030)

theorem nb073_wpp_notmem_0201 (y : Var) : y ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb073_compact_fv_empty_0031 y)

theorem nb073_wpp_notmem_0202 : (nb073_alpha_dummy_000) ∉ ((syn_cvv)).fv := by
  simpa only [nb073_alpha_dummy_000, fv_syn_cvv] using (nb073_compact_fv_empty_0032)

theorem nb073_wpp_notmem_0203 (x : Var) : x ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb073_compact_fv_empty_0033 x)

theorem nb073_wpp_notmem_0204 : (nb073_alpha_dummy_004) ∉ ((syn_cvv)).fv := by
  simpa only [nb073_alpha_dummy_004, fv_syn_cvv] using (nb073_compact_fv_empty_0034)

theorem nb073_wpp_notmem_0205 (x : Var) (y : Var) : (nb073_alpha_dummy_005 x y) ∉ ((syn_cvv)).fv := by
  simpa only [nb073_alpha_dummy_005, fv_syn_cvv] using (nb073_compact_fv_empty_0035 x y)

theorem nb073_compact_envfresh_0014 (x : Var) (y : Var) : TEnvFresh [((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb073_alpha_dummy_002) (nb073_alpha_dummy_003 x y) (nb073_wpp_notmem_0198) (nb073_wpp_notmem_0199 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_001) y (nb073_wpp_notmem_0200) (nb073_wpp_notmem_0201 y) (TEnvFresh.consFresh (nb073_alpha_dummy_000) x (nb073_wpp_notmem_0202) (nb073_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb073_alpha_dummy_004) (nb073_alpha_dummy_005 x y) (nb073_wpp_notmem_0204) (nb073_wpp_notmem_0205 x y) (TEnvFresh.nil ((syn_cvv)).fv)))))

noncomputable def nb073_wpp_refl_0014 (x : Var) (y : Var) : TReflOn [((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb073_compact_envfresh_0014 x y)

theorem nb073_compact_fv_empty_0060 : (nb073_alpha_dummy_096) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0206 : (nb073_alpha_dummy_096) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_096, fv_syn_c1c] using (nb073_compact_fv_empty_0060)

theorem nb073_compact_fv_empty_0061 (x : Var) (y : Var) : (nb073_alpha_dummy_099 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0207 (x : Var) (y : Var) : (nb073_alpha_dummy_099 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_099, fv_syn_c1c] using (nb073_compact_fv_empty_0061 x y)

theorem nb073_compact_fv_empty_0062 : (nb073_alpha_dummy_095) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0208 : (nb073_alpha_dummy_095) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_095, fv_syn_c1c] using (nb073_compact_fv_empty_0062)

theorem nb073_compact_fv_empty_0063 (x : Var) (y : Var) : (nb073_alpha_dummy_098 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0209 (x : Var) (y : Var) : (nb073_alpha_dummy_098 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_098, fv_syn_c1c] using (nb073_compact_fv_empty_0063 x y)

theorem nb073_compact_fv_empty_0064 : (nb073_alpha_dummy_094) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0210 : (nb073_alpha_dummy_094) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_094, fv_syn_c1c] using (nb073_compact_fv_empty_0064)

theorem nb073_compact_fv_empty_0065 (x : Var) (y : Var) : (nb073_alpha_dummy_097 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0211 (x : Var) (y : Var) : (nb073_alpha_dummy_097 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_097, fv_syn_c1c] using (nb073_compact_fv_empty_0065 x y)

theorem nb073_compact_fv_empty_0066 : (nb073_alpha_dummy_092) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0212 : (nb073_alpha_dummy_092) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_092, fv_syn_c1c] using (nb073_compact_fv_empty_0066)

theorem nb073_compact_fv_empty_0067 (x : Var) (y : Var) : (nb073_alpha_dummy_093 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0213 (x : Var) (y : Var) : (nb073_alpha_dummy_093 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_093, fv_syn_c1c] using (nb073_compact_fv_empty_0067 x y)

theorem nb073_compact_fv_empty_0068 : (nb073_alpha_dummy_088) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0214 : (nb073_alpha_dummy_088) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_088, fv_syn_c1c] using (nb073_compact_fv_empty_0068)

theorem nb073_compact_fv_empty_0069 (x : Var) (y : Var) : (nb073_alpha_dummy_090 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0215 (x : Var) (y : Var) : (nb073_alpha_dummy_090 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_090, fv_syn_c1c] using (nb073_compact_fv_empty_0069 x y)

theorem nb073_compact_fv_empty_0070 : (nb073_alpha_dummy_089) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0216 : (nb073_alpha_dummy_089) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_089, fv_syn_c1c] using (nb073_compact_fv_empty_0070)

theorem nb073_compact_fv_empty_0071 (x : Var) (y : Var) : (nb073_alpha_dummy_091 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0217 (x : Var) (y : Var) : (nb073_alpha_dummy_091 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_091, fv_syn_c1c] using (nb073_compact_fv_empty_0071 x y)

theorem nb073_compact_fv_empty_0072 : (nb073_alpha_dummy_081) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0218 : (nb073_alpha_dummy_081) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_081, fv_syn_c1c] using (nb073_compact_fv_empty_0072)

theorem nb073_compact_fv_empty_0073 (x : Var) (y : Var) : (nb073_alpha_dummy_083 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0219 (x : Var) (y : Var) : (nb073_alpha_dummy_083 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_083, fv_syn_c1c] using (nb073_compact_fv_empty_0073 x y)

theorem nb073_compact_fv_empty_0074 : (nb073_alpha_dummy_080) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0220 : (nb073_alpha_dummy_080) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_080, fv_syn_c1c] using (nb073_compact_fv_empty_0074)

theorem nb073_compact_fv_empty_0075 (x : Var) (y : Var) : (nb073_alpha_dummy_082 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0221 (x : Var) (y : Var) : (nb073_alpha_dummy_082 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_082, fv_syn_c1c] using (nb073_compact_fv_empty_0075 x y)

theorem nb073_compact_fv_empty_0076 : (nb073_alpha_dummy_086) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0222 : (nb073_alpha_dummy_086) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_086, fv_syn_c1c] using (nb073_compact_fv_empty_0076)

theorem nb073_compact_fv_empty_0077 (x : Var) (y : Var) : (nb073_alpha_dummy_087 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0223 (x : Var) (y : Var) : (nb073_alpha_dummy_087 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_087, fv_syn_c1c] using (nb073_compact_fv_empty_0077 x y)

theorem nb073_compact_fv_empty_0078 : (nb073_alpha_dummy_084) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0224 : (nb073_alpha_dummy_084) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_084, fv_syn_c1c] using (nb073_compact_fv_empty_0078)

theorem nb073_compact_fv_empty_0079 (x : Var) (y : Var) : (nb073_alpha_dummy_085 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0225 (x : Var) (y : Var) : (nb073_alpha_dummy_085 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_085, fv_syn_c1c] using (nb073_compact_fv_empty_0079 x y)

theorem nb073_compact_fv_empty_0080 : (nb073_alpha_dummy_078) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0226 : (nb073_alpha_dummy_078) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_078, fv_syn_c1c] using (nb073_compact_fv_empty_0080)

theorem nb073_compact_fv_empty_0081 (x : Var) (y : Var) : (nb073_alpha_dummy_079 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0227 (x : Var) (y : Var) : (nb073_alpha_dummy_079 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_079, fv_syn_c1c] using (nb073_compact_fv_empty_0081 x y)

theorem nb073_compact_envfresh_0015 (x : Var) (y : Var) : TEnvFresh [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095), (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)), ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb073_alpha_dummy_096) (nb073_alpha_dummy_099 x y) (nb073_wpp_notmem_0206) (nb073_wpp_notmem_0207 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_095) (nb073_alpha_dummy_098 x y) (nb073_wpp_notmem_0208) (nb073_wpp_notmem_0209 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_094) (nb073_alpha_dummy_097 x y) (nb073_wpp_notmem_0210) (nb073_wpp_notmem_0211 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_092) (nb073_alpha_dummy_093 x y) (nb073_wpp_notmem_0212) (nb073_wpp_notmem_0213 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_088) (nb073_alpha_dummy_090 x y) (nb073_wpp_notmem_0214) (nb073_wpp_notmem_0215 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_089) (nb073_alpha_dummy_091 x y) (nb073_wpp_notmem_0216) (nb073_wpp_notmem_0217 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_081) (nb073_alpha_dummy_083 x y) (nb073_wpp_notmem_0218) (nb073_wpp_notmem_0219 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_080) (nb073_alpha_dummy_082 x y) (nb073_wpp_notmem_0220) (nb073_wpp_notmem_0221 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_086) (nb073_alpha_dummy_087 x y) (nb073_wpp_notmem_0222) (nb073_wpp_notmem_0223 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_084) (nb073_alpha_dummy_085 x y) (nb073_wpp_notmem_0224) (nb073_wpp_notmem_0225 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_015) (nb073_alpha_dummy_017 x y) (nb073_wpp_notmem_0012) (nb073_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_014) (nb073_alpha_dummy_016 x y) (nb073_wpp_notmem_0014) (nb073_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_078) (nb073_alpha_dummy_079 x y) (nb073_wpp_notmem_0226) (nb073_wpp_notmem_0227 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_002) (nb073_alpha_dummy_003 x y) (nb073_wpp_notmem_0028) (nb073_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_001) y (nb073_wpp_notmem_0030) (nb073_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb073_alpha_dummy_000) x (nb073_wpp_notmem_0032) (nb073_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb073_alpha_dummy_004) (nb073_alpha_dummy_005 x y) (nb073_wpp_notmem_0034) (nb073_wpp_notmem_0035 x y) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb073_wpp_refl_0015 (x : Var) (y : Var) : TReflOn [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095), (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)), ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb073_compact_envfresh_0015 x y)

theorem nb073_wpp_notmem_0228 : (nb073_alpha_dummy_096) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_096, fv_syn_c0] using (nb073_compact_fv_empty_0060)

theorem nb073_wpp_notmem_0229 (x : Var) (y : Var) : (nb073_alpha_dummy_099 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_099, fv_syn_c0] using (nb073_compact_fv_empty_0061 x y)

theorem nb073_wpp_notmem_0230 : (nb073_alpha_dummy_095) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_095, fv_syn_c0] using (nb073_compact_fv_empty_0062)

theorem nb073_wpp_notmem_0231 (x : Var) (y : Var) : (nb073_alpha_dummy_098 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_098, fv_syn_c0] using (nb073_compact_fv_empty_0063 x y)

theorem nb073_wpp_notmem_0232 : (nb073_alpha_dummy_094) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_094, fv_syn_c0] using (nb073_compact_fv_empty_0064)

theorem nb073_wpp_notmem_0233 (x : Var) (y : Var) : (nb073_alpha_dummy_097 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_097, fv_syn_c0] using (nb073_compact_fv_empty_0065 x y)

theorem nb073_wpp_notmem_0234 : (nb073_alpha_dummy_092) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_092, fv_syn_c0] using (nb073_compact_fv_empty_0066)

theorem nb073_wpp_notmem_0235 (x : Var) (y : Var) : (nb073_alpha_dummy_093 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_093, fv_syn_c0] using (nb073_compact_fv_empty_0067 x y)

theorem nb073_wpp_notmem_0236 : (nb073_alpha_dummy_088) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_088, fv_syn_c0] using (nb073_compact_fv_empty_0068)

theorem nb073_wpp_notmem_0237 (x : Var) (y : Var) : (nb073_alpha_dummy_090 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_090, fv_syn_c0] using (nb073_compact_fv_empty_0069 x y)

theorem nb073_wpp_notmem_0238 : (nb073_alpha_dummy_089) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_089, fv_syn_c0] using (nb073_compact_fv_empty_0070)

theorem nb073_wpp_notmem_0239 (x : Var) (y : Var) : (nb073_alpha_dummy_091 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_091, fv_syn_c0] using (nb073_compact_fv_empty_0071 x y)

theorem nb073_wpp_notmem_0240 : (nb073_alpha_dummy_081) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_081, fv_syn_c0] using (nb073_compact_fv_empty_0072)

theorem nb073_wpp_notmem_0241 (x : Var) (y : Var) : (nb073_alpha_dummy_083 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_083, fv_syn_c0] using (nb073_compact_fv_empty_0073 x y)

theorem nb073_wpp_notmem_0242 : (nb073_alpha_dummy_080) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_080, fv_syn_c0] using (nb073_compact_fv_empty_0074)

theorem nb073_wpp_notmem_0243 (x : Var) (y : Var) : (nb073_alpha_dummy_082 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_082, fv_syn_c0] using (nb073_compact_fv_empty_0075 x y)

theorem nb073_wpp_notmem_0244 : (nb073_alpha_dummy_086) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_086, fv_syn_c0] using (nb073_compact_fv_empty_0076)

theorem nb073_wpp_notmem_0245 (x : Var) (y : Var) : (nb073_alpha_dummy_087 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_087, fv_syn_c0] using (nb073_compact_fv_empty_0077 x y)

theorem nb073_wpp_notmem_0246 : (nb073_alpha_dummy_084) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_084, fv_syn_c0] using (nb073_compact_fv_empty_0078)

theorem nb073_wpp_notmem_0247 (x : Var) (y : Var) : (nb073_alpha_dummy_085 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_085, fv_syn_c0] using (nb073_compact_fv_empty_0079 x y)

theorem nb073_wpp_notmem_0248 : (nb073_alpha_dummy_078) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_078, fv_syn_c0] using (nb073_compact_fv_empty_0080)

theorem nb073_wpp_notmem_0249 (x : Var) (y : Var) : (nb073_alpha_dummy_079 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb073_alpha_dummy_079, fv_syn_c0] using (nb073_compact_fv_empty_0081 x y)

theorem nb073_compact_envfresh_0016 (x : Var) (y : Var) : TEnvFresh [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095), (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)), ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb073_alpha_dummy_096) (nb073_alpha_dummy_099 x y) (nb073_wpp_notmem_0228) (nb073_wpp_notmem_0229 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_095) (nb073_alpha_dummy_098 x y) (nb073_wpp_notmem_0230) (nb073_wpp_notmem_0231 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_094) (nb073_alpha_dummy_097 x y) (nb073_wpp_notmem_0232) (nb073_wpp_notmem_0233 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_092) (nb073_alpha_dummy_093 x y) (nb073_wpp_notmem_0234) (nb073_wpp_notmem_0235 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_088) (nb073_alpha_dummy_090 x y) (nb073_wpp_notmem_0236) (nb073_wpp_notmem_0237 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_089) (nb073_alpha_dummy_091 x y) (nb073_wpp_notmem_0238) (nb073_wpp_notmem_0239 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_081) (nb073_alpha_dummy_083 x y) (nb073_wpp_notmem_0240) (nb073_wpp_notmem_0241 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_080) (nb073_alpha_dummy_082 x y) (nb073_wpp_notmem_0242) (nb073_wpp_notmem_0243 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_086) (nb073_alpha_dummy_087 x y) (nb073_wpp_notmem_0244) (nb073_wpp_notmem_0245 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_084) (nb073_alpha_dummy_085 x y) (nb073_wpp_notmem_0246) (nb073_wpp_notmem_0247 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_015) (nb073_alpha_dummy_017 x y) (nb073_wpp_notmem_0048) (nb073_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_014) (nb073_alpha_dummy_016 x y) (nb073_wpp_notmem_0050) (nb073_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_078) (nb073_alpha_dummy_079 x y) (nb073_wpp_notmem_0248) (nb073_wpp_notmem_0249 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_002) (nb073_alpha_dummy_003 x y) (nb073_wpp_notmem_0064) (nb073_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_001) y (nb073_wpp_notmem_0066) (nb073_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb073_alpha_dummy_000) x (nb073_wpp_notmem_0068) (nb073_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb073_alpha_dummy_004) (nb073_alpha_dummy_005 x y) (nb073_wpp_notmem_0070) (nb073_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb073_wpp_refl_0016 (x : Var) (y : Var) : TReflOn [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095), (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)), ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb073_compact_envfresh_0016 x y)

theorem nb073_wpp_notmem_0250 : (nb073_alpha_dummy_092) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_092, fv_syn_cnnc] using (nb073_compact_fv_empty_0066)

theorem nb073_wpp_notmem_0251 (x : Var) (y : Var) : (nb073_alpha_dummy_093 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_093, fv_syn_cnnc] using (nb073_compact_fv_empty_0067 x y)

theorem nb073_wpp_notmem_0252 : (nb073_alpha_dummy_088) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_088, fv_syn_cnnc] using (nb073_compact_fv_empty_0068)

theorem nb073_wpp_notmem_0253 (x : Var) (y : Var) : (nb073_alpha_dummy_090 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_090, fv_syn_cnnc] using (nb073_compact_fv_empty_0069 x y)

theorem nb073_wpp_notmem_0254 : (nb073_alpha_dummy_089) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_089, fv_syn_cnnc] using (nb073_compact_fv_empty_0070)

theorem nb073_wpp_notmem_0255 (x : Var) (y : Var) : (nb073_alpha_dummy_091 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_091, fv_syn_cnnc] using (nb073_compact_fv_empty_0071 x y)

theorem nb073_wpp_notmem_0256 : (nb073_alpha_dummy_081) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_081, fv_syn_cnnc] using (nb073_compact_fv_empty_0072)

theorem nb073_wpp_notmem_0257 (x : Var) (y : Var) : (nb073_alpha_dummy_083 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_083, fv_syn_cnnc] using (nb073_compact_fv_empty_0073 x y)

theorem nb073_wpp_notmem_0258 : (nb073_alpha_dummy_080) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_080, fv_syn_cnnc] using (nb073_compact_fv_empty_0074)

theorem nb073_wpp_notmem_0259 (x : Var) (y : Var) : (nb073_alpha_dummy_082 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_082, fv_syn_cnnc] using (nb073_compact_fv_empty_0075 x y)

theorem nb073_wpp_notmem_0260 : (nb073_alpha_dummy_086) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_086, fv_syn_cnnc] using (nb073_compact_fv_empty_0076)

theorem nb073_wpp_notmem_0261 (x : Var) (y : Var) : (nb073_alpha_dummy_087 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_087, fv_syn_cnnc] using (nb073_compact_fv_empty_0077 x y)

theorem nb073_wpp_notmem_0262 : (nb073_alpha_dummy_084) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_084, fv_syn_cnnc] using (nb073_compact_fv_empty_0078)

theorem nb073_wpp_notmem_0263 (x : Var) (y : Var) : (nb073_alpha_dummy_085 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_085, fv_syn_cnnc] using (nb073_compact_fv_empty_0079 x y)

theorem nb073_wpp_notmem_0264 : (nb073_alpha_dummy_078) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_078, fv_syn_cnnc] using (nb073_compact_fv_empty_0080)

theorem nb073_wpp_notmem_0265 (x : Var) (y : Var) : (nb073_alpha_dummy_079 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb073_alpha_dummy_079, fv_syn_cnnc] using (nb073_compact_fv_empty_0081 x y)

theorem nb073_compact_envfresh_0017 (x : Var) (y : Var) : TEnvFresh [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb073_alpha_dummy_092) (nb073_alpha_dummy_093 x y) (nb073_wpp_notmem_0250) (nb073_wpp_notmem_0251 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_088) (nb073_alpha_dummy_090 x y) (nb073_wpp_notmem_0252) (nb073_wpp_notmem_0253 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_089) (nb073_alpha_dummy_091 x y) (nb073_wpp_notmem_0254) (nb073_wpp_notmem_0255 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_081) (nb073_alpha_dummy_083 x y) (nb073_wpp_notmem_0256) (nb073_wpp_notmem_0257 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_080) (nb073_alpha_dummy_082 x y) (nb073_wpp_notmem_0258) (nb073_wpp_notmem_0259 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_086) (nb073_alpha_dummy_087 x y) (nb073_wpp_notmem_0260) (nb073_wpp_notmem_0261 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_084) (nb073_alpha_dummy_085 x y) (nb073_wpp_notmem_0262) (nb073_wpp_notmem_0263 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_015) (nb073_alpha_dummy_017 x y) (nb073_wpp_notmem_0078) (nb073_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_014) (nb073_alpha_dummy_016 x y) (nb073_wpp_notmem_0080) (nb073_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_078) (nb073_alpha_dummy_079 x y) (nb073_wpp_notmem_0264) (nb073_wpp_notmem_0265 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_002) (nb073_alpha_dummy_003 x y) (nb073_wpp_notmem_0094) (nb073_wpp_notmem_0095 x y) (TEnvFresh.consFresh (nb073_alpha_dummy_001) y (nb073_wpp_notmem_0096) (nb073_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb073_alpha_dummy_000) x (nb073_wpp_notmem_0098) (nb073_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb073_alpha_dummy_004) (nb073_alpha_dummy_005 x y) (nb073_wpp_notmem_0100) (nb073_wpp_notmem_0101 x y) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb073_wpp_refl_0017 (x : Var) (y : Var) : TReflOn [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb073_compact_envfresh_0017 x y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
