import NAR4C078C001Part034

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

noncomputable def nb078_split_alpha_0003 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.classMem (Class.cv (nb078_alpha_dummy_085)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_086 f)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0049 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0049 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0079 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0077 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_054))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_056 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0053 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0053 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068), (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)), ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0010 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0055 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0059 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0055 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0059 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068), (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)), ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0011 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0063 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0063 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0067 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0067 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0012 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0012 x y f)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0049 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0049 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0079 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0077 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_054))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_056 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0053 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0053 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068), (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)), ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0010 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0055 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0059 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0055 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0059 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068), (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)), ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0011 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0063 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0063 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0067 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0067 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0012 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)), ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0012 x y f))))))))))))))))))))))))

theorem nb078_wpp_notmem_0224 : (nb078_alpha_dummy_085) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_085, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0066)

theorem nb078_wpp_notmem_0225 (f : Var) : (nb078_alpha_dummy_086 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_086, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0067 f)

theorem nb078_wpp_notmem_0226 : (nb078_alpha_dummy_054) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_054, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0054)

theorem nb078_wpp_notmem_0227 (f : Var) : (nb078_alpha_dummy_056 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_056, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0055 f)

theorem nb078_wpp_notmem_0228 : (nb078_alpha_dummy_053) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_053, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0056)

theorem nb078_wpp_notmem_0229 (f : Var) : (nb078_alpha_dummy_055 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_055, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0057 f)

theorem nb078_wpp_notmem_0230 : (nb078_alpha_dummy_083) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_083, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0068)

theorem nb078_wpp_notmem_0231 (f : Var) : (nb078_alpha_dummy_084 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_084, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0069 f)

theorem nb078_wpp_notmem_0232 : (nb078_alpha_dummy_057) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_057, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0060)

theorem nb078_wpp_notmem_0233 (f : Var) : (nb078_alpha_dummy_058 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_058, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0061 f)

theorem nb078_wpp_notmem_0234 : (nb078_alpha_dummy_011) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_011, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0062)

theorem nb078_wpp_notmem_0235 (f : Var) : (nb078_alpha_dummy_014 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_014, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0063 f)

theorem nb078_compact_envfresh_0013 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_085) (nb078_alpha_dummy_086 f) (nb078_wpp_notmem_0224) (nb078_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb078_alpha_dummy_054) (nb078_alpha_dummy_056 f) (nb078_wpp_notmem_0226) (nb078_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb078_alpha_dummy_053) (nb078_alpha_dummy_055 f) (nb078_wpp_notmem_0228) (nb078_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb078_alpha_dummy_083) (nb078_alpha_dummy_084 f) (nb078_wpp_notmem_0230) (nb078_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb078_alpha_dummy_057) (nb078_alpha_dummy_058 f) (nb078_wpp_notmem_0232) (nb078_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0234) (nb078_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0130) (nb078_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0132) (nb078_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0134) (nb078_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0136) (nb078_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0138) (nb078_wpp_notmem_0139 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0140) (nb078_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb078_wpp_refl_0013 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0013 x y f)

theorem nb078_compact_fv_empty_0070 : (nb078_alpha_dummy_111) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0236 : (nb078_alpha_dummy_111) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_111, fv_syn_c1c] using (nb078_compact_fv_empty_0070)

theorem nb078_compact_fv_empty_0071 (f : Var) : (nb078_alpha_dummy_114 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0237 (f : Var) : (nb078_alpha_dummy_114 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_114, fv_syn_c1c] using (nb078_compact_fv_empty_0071 f)

theorem nb078_compact_fv_empty_0072 : (nb078_alpha_dummy_110) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0238 : (nb078_alpha_dummy_110) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_110, fv_syn_c1c] using (nb078_compact_fv_empty_0072)

theorem nb078_compact_fv_empty_0073 (f : Var) : (nb078_alpha_dummy_113 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0239 (f : Var) : (nb078_alpha_dummy_113 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_113, fv_syn_c1c] using (nb078_compact_fv_empty_0073 f)

theorem nb078_compact_fv_empty_0074 : (nb078_alpha_dummy_109) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0240 : (nb078_alpha_dummy_109) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_109, fv_syn_c1c] using (nb078_compact_fv_empty_0074)

theorem nb078_compact_fv_empty_0075 (f : Var) : (nb078_alpha_dummy_112 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0241 (f : Var) : (nb078_alpha_dummy_112 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_112, fv_syn_c1c] using (nb078_compact_fv_empty_0075 f)

theorem nb078_compact_fv_empty_0076 : (nb078_alpha_dummy_107) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0242 : (nb078_alpha_dummy_107) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_107, fv_syn_c1c] using (nb078_compact_fv_empty_0076)

theorem nb078_compact_fv_empty_0077 (f : Var) : (nb078_alpha_dummy_108 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0243 (f : Var) : (nb078_alpha_dummy_108 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_108, fv_syn_c1c] using (nb078_compact_fv_empty_0077 f)

theorem nb078_compact_fv_empty_0078 : (nb078_alpha_dummy_103) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0244 : (nb078_alpha_dummy_103) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_103, fv_syn_c1c] using (nb078_compact_fv_empty_0078)

theorem nb078_compact_fv_empty_0079 (f : Var) : (nb078_alpha_dummy_105 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0245 (f : Var) : (nb078_alpha_dummy_105 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_105, fv_syn_c1c] using (nb078_compact_fv_empty_0079 f)

theorem nb078_compact_fv_empty_0080 : (nb078_alpha_dummy_104) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0246 : (nb078_alpha_dummy_104) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_104, fv_syn_c1c] using (nb078_compact_fv_empty_0080)

theorem nb078_compact_fv_empty_0081 (f : Var) : (nb078_alpha_dummy_106 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0247 (f : Var) : (nb078_alpha_dummy_106 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_106, fv_syn_c1c] using (nb078_compact_fv_empty_0081 f)

theorem nb078_compact_fv_empty_0082 : (nb078_alpha_dummy_096) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0248 : (nb078_alpha_dummy_096) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_096, fv_syn_c1c] using (nb078_compact_fv_empty_0082)

theorem nb078_compact_fv_empty_0083 (f : Var) : (nb078_alpha_dummy_098 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0249 (f : Var) : (nb078_alpha_dummy_098 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_098, fv_syn_c1c] using (nb078_compact_fv_empty_0083 f)

theorem nb078_compact_fv_empty_0084 : (nb078_alpha_dummy_095) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0250 : (nb078_alpha_dummy_095) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_095, fv_syn_c1c] using (nb078_compact_fv_empty_0084)

theorem nb078_compact_fv_empty_0085 (f : Var) : (nb078_alpha_dummy_097 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0251 (f : Var) : (nb078_alpha_dummy_097 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_097, fv_syn_c1c] using (nb078_compact_fv_empty_0085 f)

theorem nb078_compact_fv_empty_0086 : (nb078_alpha_dummy_101) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0252 : (nb078_alpha_dummy_101) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_101, fv_syn_c1c] using (nb078_compact_fv_empty_0086)

theorem nb078_compact_fv_empty_0087 (f : Var) : (nb078_alpha_dummy_102 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0253 (f : Var) : (nb078_alpha_dummy_102 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_102, fv_syn_c1c] using (nb078_compact_fv_empty_0087 f)

theorem nb078_compact_fv_empty_0088 : (nb078_alpha_dummy_099) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0254 : (nb078_alpha_dummy_099) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_099, fv_syn_c1c] using (nb078_compact_fv_empty_0088)

theorem nb078_compact_fv_empty_0089 (f : Var) : (nb078_alpha_dummy_100 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0255 (f : Var) : (nb078_alpha_dummy_100 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_100, fv_syn_c1c] using (nb078_compact_fv_empty_0089 f)

theorem nb078_compact_fv_empty_0090 : (nb078_alpha_dummy_090) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0256 : (nb078_alpha_dummy_090) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_090, fv_syn_c1c] using (nb078_compact_fv_empty_0090)

theorem nb078_compact_fv_empty_0091 (f : Var) : (nb078_alpha_dummy_092 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0257 (f : Var) : (nb078_alpha_dummy_092 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_092, fv_syn_c1c] using (nb078_compact_fv_empty_0091 f)

theorem nb078_compact_fv_empty_0092 : (nb078_alpha_dummy_089) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0258 : (nb078_alpha_dummy_089) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_089, fv_syn_c1c] using (nb078_compact_fv_empty_0092)

theorem nb078_compact_fv_empty_0093 (f : Var) : (nb078_alpha_dummy_091 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0259 (f : Var) : (nb078_alpha_dummy_091 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_091, fv_syn_c1c] using (nb078_compact_fv_empty_0093 f)

theorem nb078_compact_fv_empty_0094 : (nb078_alpha_dummy_093) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0260 : (nb078_alpha_dummy_093) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_093, fv_syn_c1c] using (nb078_compact_fv_empty_0094)

theorem nb078_compact_fv_empty_0095 (f : Var) : (nb078_alpha_dummy_094 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0261 (f : Var) : (nb078_alpha_dummy_094 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_094, fv_syn_c1c] using (nb078_compact_fv_empty_0095 f)

theorem nb078_compact_envfresh_0014 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_111) (nb078_alpha_dummy_114 f) (nb078_wpp_notmem_0236) (nb078_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb078_alpha_dummy_110) (nb078_alpha_dummy_113 f) (nb078_wpp_notmem_0238) (nb078_wpp_notmem_0239 f) (TEnvFresh.consFresh (nb078_alpha_dummy_109) (nb078_alpha_dummy_112 f) (nb078_wpp_notmem_0240) (nb078_wpp_notmem_0241 f) (TEnvFresh.consFresh (nb078_alpha_dummy_107) (nb078_alpha_dummy_108 f) (nb078_wpp_notmem_0242) (nb078_wpp_notmem_0243 f) (TEnvFresh.consFresh (nb078_alpha_dummy_103) (nb078_alpha_dummy_105 f) (nb078_wpp_notmem_0244) (nb078_wpp_notmem_0245 f) (TEnvFresh.consFresh (nb078_alpha_dummy_104) (nb078_alpha_dummy_106 f) (nb078_wpp_notmem_0246) (nb078_wpp_notmem_0247 f) (TEnvFresh.consFresh (nb078_alpha_dummy_096) (nb078_alpha_dummy_098 f) (nb078_wpp_notmem_0248) (nb078_wpp_notmem_0249 f) (TEnvFresh.consFresh (nb078_alpha_dummy_095) (nb078_alpha_dummy_097 f) (nb078_wpp_notmem_0250) (nb078_wpp_notmem_0251 f) (TEnvFresh.consFresh (nb078_alpha_dummy_101) (nb078_alpha_dummy_102 f) (nb078_wpp_notmem_0252) (nb078_wpp_notmem_0253 f) (TEnvFresh.consFresh (nb078_alpha_dummy_099) (nb078_alpha_dummy_100 f) (nb078_wpp_notmem_0254) (nb078_wpp_notmem_0255 f) (TEnvFresh.consFresh (nb078_alpha_dummy_090) (nb078_alpha_dummy_092 f) (nb078_wpp_notmem_0256) (nb078_wpp_notmem_0257 f) (TEnvFresh.consFresh (nb078_alpha_dummy_089) (nb078_alpha_dummy_091 f) (nb078_wpp_notmem_0258) (nb078_wpp_notmem_0259 f) (TEnvFresh.consFresh (nb078_alpha_dummy_093) (nb078_alpha_dummy_094 f) (nb078_wpp_notmem_0260) (nb078_wpp_notmem_0261 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0166) (nb078_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0020) (nb078_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0022) (nb078_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0024) (nb078_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0026) (nb078_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0028) (nb078_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0030) (nb078_wpp_notmem_0031 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0014 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0014 x y f)

theorem nb078_wpp_notmem_0262 : (nb078_alpha_dummy_111) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_111, fv_syn_c0] using (nb078_compact_fv_empty_0070)

theorem nb078_wpp_notmem_0263 (f : Var) : (nb078_alpha_dummy_114 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_114, fv_syn_c0] using (nb078_compact_fv_empty_0071 f)

theorem nb078_wpp_notmem_0264 : (nb078_alpha_dummy_110) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_110, fv_syn_c0] using (nb078_compact_fv_empty_0072)

theorem nb078_wpp_notmem_0265 (f : Var) : (nb078_alpha_dummy_113 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_113, fv_syn_c0] using (nb078_compact_fv_empty_0073 f)

theorem nb078_wpp_notmem_0266 : (nb078_alpha_dummy_109) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_109, fv_syn_c0] using (nb078_compact_fv_empty_0074)

theorem nb078_wpp_notmem_0267 (f : Var) : (nb078_alpha_dummy_112 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_112, fv_syn_c0] using (nb078_compact_fv_empty_0075 f)

theorem nb078_wpp_notmem_0268 : (nb078_alpha_dummy_107) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_107, fv_syn_c0] using (nb078_compact_fv_empty_0076)

theorem nb078_wpp_notmem_0269 (f : Var) : (nb078_alpha_dummy_108 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_108, fv_syn_c0] using (nb078_compact_fv_empty_0077 f)

theorem nb078_wpp_notmem_0270 : (nb078_alpha_dummy_103) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_103, fv_syn_c0] using (nb078_compact_fv_empty_0078)

theorem nb078_wpp_notmem_0271 (f : Var) : (nb078_alpha_dummy_105 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_105, fv_syn_c0] using (nb078_compact_fv_empty_0079 f)

theorem nb078_wpp_notmem_0272 : (nb078_alpha_dummy_104) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_104, fv_syn_c0] using (nb078_compact_fv_empty_0080)

theorem nb078_wpp_notmem_0273 (f : Var) : (nb078_alpha_dummy_106 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_106, fv_syn_c0] using (nb078_compact_fv_empty_0081 f)

theorem nb078_wpp_notmem_0274 : (nb078_alpha_dummy_096) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_096, fv_syn_c0] using (nb078_compact_fv_empty_0082)

theorem nb078_wpp_notmem_0275 (f : Var) : (nb078_alpha_dummy_098 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_098, fv_syn_c0] using (nb078_compact_fv_empty_0083 f)

theorem nb078_wpp_notmem_0276 : (nb078_alpha_dummy_095) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_095, fv_syn_c0] using (nb078_compact_fv_empty_0084)

theorem nb078_wpp_notmem_0277 (f : Var) : (nb078_alpha_dummy_097 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_097, fv_syn_c0] using (nb078_compact_fv_empty_0085 f)

theorem nb078_wpp_notmem_0278 : (nb078_alpha_dummy_101) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_101, fv_syn_c0] using (nb078_compact_fv_empty_0086)

theorem nb078_wpp_notmem_0279 (f : Var) : (nb078_alpha_dummy_102 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_102, fv_syn_c0] using (nb078_compact_fv_empty_0087 f)

theorem nb078_wpp_notmem_0280 : (nb078_alpha_dummy_099) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_099, fv_syn_c0] using (nb078_compact_fv_empty_0088)

theorem nb078_wpp_notmem_0281 (f : Var) : (nb078_alpha_dummy_100 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_100, fv_syn_c0] using (nb078_compact_fv_empty_0089 f)

theorem nb078_wpp_notmem_0282 : (nb078_alpha_dummy_090) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_090, fv_syn_c0] using (nb078_compact_fv_empty_0090)

theorem nb078_wpp_notmem_0283 (f : Var) : (nb078_alpha_dummy_092 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_092, fv_syn_c0] using (nb078_compact_fv_empty_0091 f)

theorem nb078_wpp_notmem_0284 : (nb078_alpha_dummy_089) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_089, fv_syn_c0] using (nb078_compact_fv_empty_0092)

theorem nb078_wpp_notmem_0285 (f : Var) : (nb078_alpha_dummy_091 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_091, fv_syn_c0] using (nb078_compact_fv_empty_0093 f)

theorem nb078_wpp_notmem_0286 : (nb078_alpha_dummy_093) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_093, fv_syn_c0] using (nb078_compact_fv_empty_0094)

theorem nb078_wpp_notmem_0287 (f : Var) : (nb078_alpha_dummy_094 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_094, fv_syn_c0] using (nb078_compact_fv_empty_0095 f)

theorem nb078_compact_envfresh_0015 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_111) (nb078_alpha_dummy_114 f) (nb078_wpp_notmem_0262) (nb078_wpp_notmem_0263 f) (TEnvFresh.consFresh (nb078_alpha_dummy_110) (nb078_alpha_dummy_113 f) (nb078_wpp_notmem_0264) (nb078_wpp_notmem_0265 f) (TEnvFresh.consFresh (nb078_alpha_dummy_109) (nb078_alpha_dummy_112 f) (nb078_wpp_notmem_0266) (nb078_wpp_notmem_0267 f) (TEnvFresh.consFresh (nb078_alpha_dummy_107) (nb078_alpha_dummy_108 f) (nb078_wpp_notmem_0268) (nb078_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb078_alpha_dummy_103) (nb078_alpha_dummy_105 f) (nb078_wpp_notmem_0270) (nb078_wpp_notmem_0271 f) (TEnvFresh.consFresh (nb078_alpha_dummy_104) (nb078_alpha_dummy_106 f) (nb078_wpp_notmem_0272) (nb078_wpp_notmem_0273 f) (TEnvFresh.consFresh (nb078_alpha_dummy_096) (nb078_alpha_dummy_098 f) (nb078_wpp_notmem_0274) (nb078_wpp_notmem_0275 f) (TEnvFresh.consFresh (nb078_alpha_dummy_095) (nb078_alpha_dummy_097 f) (nb078_wpp_notmem_0276) (nb078_wpp_notmem_0277 f) (TEnvFresh.consFresh (nb078_alpha_dummy_101) (nb078_alpha_dummy_102 f) (nb078_wpp_notmem_0278) (nb078_wpp_notmem_0279 f) (TEnvFresh.consFresh (nb078_alpha_dummy_099) (nb078_alpha_dummy_100 f) (nb078_wpp_notmem_0280) (nb078_wpp_notmem_0281 f) (TEnvFresh.consFresh (nb078_alpha_dummy_090) (nb078_alpha_dummy_092 f) (nb078_wpp_notmem_0282) (nb078_wpp_notmem_0283 f) (TEnvFresh.consFresh (nb078_alpha_dummy_089) (nb078_alpha_dummy_091 f) (nb078_wpp_notmem_0284) (nb078_wpp_notmem_0285 f) (TEnvFresh.consFresh (nb078_alpha_dummy_093) (nb078_alpha_dummy_094 f) (nb078_wpp_notmem_0286) (nb078_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0188) (nb078_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0056) (nb078_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0058) (nb078_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0060) (nb078_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0062) (nb078_wpp_notmem_0063 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0064) (nb078_wpp_notmem_0065 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0066) (nb078_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0015 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0015 x y f)

theorem nb078_wpp_notmem_0288 : (nb078_alpha_dummy_107) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_107, fv_syn_cnnc] using (nb078_compact_fv_empty_0076)

theorem nb078_wpp_notmem_0289 (f : Var) : (nb078_alpha_dummy_108 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_108, fv_syn_cnnc] using (nb078_compact_fv_empty_0077 f)

theorem nb078_wpp_notmem_0290 : (nb078_alpha_dummy_103) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_103, fv_syn_cnnc] using (nb078_compact_fv_empty_0078)

theorem nb078_wpp_notmem_0291 (f : Var) : (nb078_alpha_dummy_105 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_105, fv_syn_cnnc] using (nb078_compact_fv_empty_0079 f)

theorem nb078_wpp_notmem_0292 : (nb078_alpha_dummy_104) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_104, fv_syn_cnnc] using (nb078_compact_fv_empty_0080)

theorem nb078_wpp_notmem_0293 (f : Var) : (nb078_alpha_dummy_106 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_106, fv_syn_cnnc] using (nb078_compact_fv_empty_0081 f)

theorem nb078_wpp_notmem_0294 : (nb078_alpha_dummy_096) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_096, fv_syn_cnnc] using (nb078_compact_fv_empty_0082)

theorem nb078_wpp_notmem_0295 (f : Var) : (nb078_alpha_dummy_098 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_098, fv_syn_cnnc] using (nb078_compact_fv_empty_0083 f)

theorem nb078_wpp_notmem_0296 : (nb078_alpha_dummy_095) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_095, fv_syn_cnnc] using (nb078_compact_fv_empty_0084)

theorem nb078_wpp_notmem_0297 (f : Var) : (nb078_alpha_dummy_097 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_097, fv_syn_cnnc] using (nb078_compact_fv_empty_0085 f)

theorem nb078_wpp_notmem_0298 : (nb078_alpha_dummy_101) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_101, fv_syn_cnnc] using (nb078_compact_fv_empty_0086)

theorem nb078_wpp_notmem_0299 (f : Var) : (nb078_alpha_dummy_102 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_102, fv_syn_cnnc] using (nb078_compact_fv_empty_0087 f)

theorem nb078_wpp_notmem_0300 : (nb078_alpha_dummy_099) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_099, fv_syn_cnnc] using (nb078_compact_fv_empty_0088)

theorem nb078_wpp_notmem_0301 (f : Var) : (nb078_alpha_dummy_100 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_100, fv_syn_cnnc] using (nb078_compact_fv_empty_0089 f)

theorem nb078_wpp_notmem_0302 : (nb078_alpha_dummy_090) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_090, fv_syn_cnnc] using (nb078_compact_fv_empty_0090)

theorem nb078_wpp_notmem_0303 (f : Var) : (nb078_alpha_dummy_092 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_092, fv_syn_cnnc] using (nb078_compact_fv_empty_0091 f)

theorem nb078_wpp_notmem_0304 : (nb078_alpha_dummy_089) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_089, fv_syn_cnnc] using (nb078_compact_fv_empty_0092)

theorem nb078_wpp_notmem_0305 (f : Var) : (nb078_alpha_dummy_091 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_091, fv_syn_cnnc] using (nb078_compact_fv_empty_0093 f)

theorem nb078_wpp_notmem_0306 : (nb078_alpha_dummy_093) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_093, fv_syn_cnnc] using (nb078_compact_fv_empty_0094)

theorem nb078_wpp_notmem_0307 (f : Var) : (nb078_alpha_dummy_094 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_094, fv_syn_cnnc] using (nb078_compact_fv_empty_0095 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
