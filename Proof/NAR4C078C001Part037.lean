import NAR4C078C001Part036

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

noncomputable def nb078_split_alpha_0005 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_129)) (syn_cphi (Class.cv (nb078_alpha_dummy_096)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_129)) (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_130 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_130 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_096))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_098 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0094) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0095 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0095 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0017 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0099 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0097 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0103 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0101 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0099 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0097 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0103 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0101 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0018 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0107 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0105 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0107 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0105 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0111 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0109 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0111 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0109 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0019 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0019 x y f)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_096))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_098 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0094) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0095 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0095 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0017 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0099 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0097 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0103 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0101 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0099 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0097 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0103 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0101 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0018 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0107 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0105 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0107 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0105 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0111 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0109 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0111 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0109 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0019 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0093 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0019 x y f))))))))))))))))))))

theorem nb078_wpp_notmem_0326 : (nb078_alpha_dummy_127) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_127, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0098)

theorem nb078_wpp_notmem_0327 (f : Var) : (nb078_alpha_dummy_128 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_128, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0099 f)

theorem nb078_wpp_notmem_0328 : (nb078_alpha_dummy_096) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_096, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0082)

theorem nb078_wpp_notmem_0329 (f : Var) : (nb078_alpha_dummy_098 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_098, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0083 f)

theorem nb078_wpp_notmem_0330 : (nb078_alpha_dummy_095) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_095, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0084)

theorem nb078_wpp_notmem_0331 (f : Var) : (nb078_alpha_dummy_097 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_097, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0085 f)

theorem nb078_wpp_notmem_0332 : (nb078_alpha_dummy_125) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_125, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0100)

theorem nb078_wpp_notmem_0333 (f : Var) : (nb078_alpha_dummy_126 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_126, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0101 f)

theorem nb078_wpp_notmem_0334 : (nb078_alpha_dummy_099) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_099, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0088)

theorem nb078_wpp_notmem_0335 (f : Var) : (nb078_alpha_dummy_100 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_100, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0089 f)

theorem nb078_wpp_notmem_0336 : (nb078_alpha_dummy_090) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_090, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0090)

theorem nb078_wpp_notmem_0337 (f : Var) : (nb078_alpha_dummy_092 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_092, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0091 f)

theorem nb078_wpp_notmem_0338 : (nb078_alpha_dummy_089) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_089, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0092)

theorem nb078_wpp_notmem_0339 (f : Var) : (nb078_alpha_dummy_091 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_091, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0093 f)

theorem nb078_wpp_notmem_0340 : (nb078_alpha_dummy_093) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_093, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0094)

theorem nb078_wpp_notmem_0341 (f : Var) : (nb078_alpha_dummy_094 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_094, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0095 f)

theorem nb078_compact_envfresh_0020 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_127) (nb078_alpha_dummy_128 f) (nb078_wpp_notmem_0326) (nb078_wpp_notmem_0327 f) (TEnvFresh.consFresh (nb078_alpha_dummy_096) (nb078_alpha_dummy_098 f) (nb078_wpp_notmem_0328) (nb078_wpp_notmem_0329 f) (TEnvFresh.consFresh (nb078_alpha_dummy_095) (nb078_alpha_dummy_097 f) (nb078_wpp_notmem_0330) (nb078_wpp_notmem_0331 f) (TEnvFresh.consFresh (nb078_alpha_dummy_125) (nb078_alpha_dummy_126 f) (nb078_wpp_notmem_0332) (nb078_wpp_notmem_0333 f) (TEnvFresh.consFresh (nb078_alpha_dummy_099) (nb078_alpha_dummy_100 f) (nb078_wpp_notmem_0334) (nb078_wpp_notmem_0335 f) (TEnvFresh.consFresh (nb078_alpha_dummy_090) (nb078_alpha_dummy_092 f) (nb078_wpp_notmem_0336) (nb078_wpp_notmem_0337 f) (TEnvFresh.consFresh (nb078_alpha_dummy_089) (nb078_alpha_dummy_091 f) (nb078_wpp_notmem_0338) (nb078_wpp_notmem_0339 f) (TEnvFresh.consFresh (nb078_alpha_dummy_093) (nb078_alpha_dummy_094 f) (nb078_wpp_notmem_0340) (nb078_wpp_notmem_0341 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0234) (nb078_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0130) (nb078_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0132) (nb078_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0134) (nb078_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0136) (nb078_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0138) (nb078_wpp_notmem_0139 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0140) (nb078_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0020 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0020 x y f)

theorem nb078_compact_fv_empty_0102 : (nb078_alpha_dummy_147) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0342 : (nb078_alpha_dummy_147) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_147, fv_syn_c1c] using (nb078_compact_fv_empty_0102)

theorem nb078_compact_fv_empty_0103 (f : Var) : (nb078_alpha_dummy_150 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0343 (f : Var) : (nb078_alpha_dummy_150 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_150, fv_syn_c1c] using (nb078_compact_fv_empty_0103 f)

theorem nb078_compact_fv_empty_0104 : (nb078_alpha_dummy_146) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0344 : (nb078_alpha_dummy_146) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_146, fv_syn_c1c] using (nb078_compact_fv_empty_0104)

theorem nb078_compact_fv_empty_0105 (f : Var) : (nb078_alpha_dummy_149 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0345 (f : Var) : (nb078_alpha_dummy_149 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_149, fv_syn_c1c] using (nb078_compact_fv_empty_0105 f)

theorem nb078_compact_fv_empty_0106 : (nb078_alpha_dummy_145) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0346 : (nb078_alpha_dummy_145) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_145, fv_syn_c1c] using (nb078_compact_fv_empty_0106)

theorem nb078_compact_fv_empty_0107 (f : Var) : (nb078_alpha_dummy_148 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0347 (f : Var) : (nb078_alpha_dummy_148 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_148, fv_syn_c1c] using (nb078_compact_fv_empty_0107 f)

theorem nb078_compact_fv_empty_0108 : (nb078_alpha_dummy_143) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0348 : (nb078_alpha_dummy_143) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_143, fv_syn_c1c] using (nb078_compact_fv_empty_0108)

theorem nb078_compact_fv_empty_0109 (f : Var) : (nb078_alpha_dummy_144 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0349 (f : Var) : (nb078_alpha_dummy_144 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_144, fv_syn_c1c] using (nb078_compact_fv_empty_0109 f)

theorem nb078_compact_fv_empty_0110 : (nb078_alpha_dummy_139) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0350 : (nb078_alpha_dummy_139) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_139, fv_syn_c1c] using (nb078_compact_fv_empty_0110)

theorem nb078_compact_fv_empty_0111 (f : Var) : (nb078_alpha_dummy_141 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0351 (f : Var) : (nb078_alpha_dummy_141 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_141, fv_syn_c1c] using (nb078_compact_fv_empty_0111 f)

theorem nb078_compact_fv_empty_0112 : (nb078_alpha_dummy_140) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0352 : (nb078_alpha_dummy_140) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_140, fv_syn_c1c] using (nb078_compact_fv_empty_0112)

theorem nb078_compact_fv_empty_0113 (f : Var) : (nb078_alpha_dummy_142 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0353 (f : Var) : (nb078_alpha_dummy_142 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_142, fv_syn_c1c] using (nb078_compact_fv_empty_0113 f)

theorem nb078_compact_fv_empty_0114 : (nb078_alpha_dummy_132) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0354 : (nb078_alpha_dummy_132) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_132, fv_syn_c1c] using (nb078_compact_fv_empty_0114)

theorem nb078_compact_fv_empty_0115 (f : Var) : (nb078_alpha_dummy_134 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0355 (f : Var) : (nb078_alpha_dummy_134 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_134, fv_syn_c1c] using (nb078_compact_fv_empty_0115 f)

theorem nb078_compact_fv_empty_0116 : (nb078_alpha_dummy_131) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0356 : (nb078_alpha_dummy_131) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_131, fv_syn_c1c] using (nb078_compact_fv_empty_0116)

theorem nb078_compact_fv_empty_0117 (f : Var) : (nb078_alpha_dummy_133 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0357 (f : Var) : (nb078_alpha_dummy_133 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_133, fv_syn_c1c] using (nb078_compact_fv_empty_0117 f)

theorem nb078_compact_fv_empty_0118 : (nb078_alpha_dummy_137) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0358 : (nb078_alpha_dummy_137) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_137, fv_syn_c1c] using (nb078_compact_fv_empty_0118)

theorem nb078_compact_fv_empty_0119 (f : Var) : (nb078_alpha_dummy_138 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0359 (f : Var) : (nb078_alpha_dummy_138 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_138, fv_syn_c1c] using (nb078_compact_fv_empty_0119 f)

theorem nb078_compact_fv_empty_0120 : (nb078_alpha_dummy_135) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0360 : (nb078_alpha_dummy_135) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_135, fv_syn_c1c] using (nb078_compact_fv_empty_0120)

theorem nb078_compact_fv_empty_0121 (f : Var) : (nb078_alpha_dummy_136 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0361 (f : Var) : (nb078_alpha_dummy_136 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_136, fv_syn_c1c] using (nb078_compact_fv_empty_0121 f)

theorem nb078_compact_envfresh_0021 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_147) (nb078_alpha_dummy_150 f) (nb078_wpp_notmem_0342) (nb078_wpp_notmem_0343 f) (TEnvFresh.consFresh (nb078_alpha_dummy_146) (nb078_alpha_dummy_149 f) (nb078_wpp_notmem_0344) (nb078_wpp_notmem_0345 f) (TEnvFresh.consFresh (nb078_alpha_dummy_145) (nb078_alpha_dummy_148 f) (nb078_wpp_notmem_0346) (nb078_wpp_notmem_0347 f) (TEnvFresh.consFresh (nb078_alpha_dummy_143) (nb078_alpha_dummy_144 f) (nb078_wpp_notmem_0348) (nb078_wpp_notmem_0349 f) (TEnvFresh.consFresh (nb078_alpha_dummy_139) (nb078_alpha_dummy_141 f) (nb078_wpp_notmem_0350) (nb078_wpp_notmem_0351 f) (TEnvFresh.consFresh (nb078_alpha_dummy_140) (nb078_alpha_dummy_142 f) (nb078_wpp_notmem_0352) (nb078_wpp_notmem_0353 f) (TEnvFresh.consFresh (nb078_alpha_dummy_132) (nb078_alpha_dummy_134 f) (nb078_wpp_notmem_0354) (nb078_wpp_notmem_0355 f) (TEnvFresh.consFresh (nb078_alpha_dummy_131) (nb078_alpha_dummy_133 f) (nb078_wpp_notmem_0356) (nb078_wpp_notmem_0357 f) (TEnvFresh.consFresh (nb078_alpha_dummy_137) (nb078_alpha_dummy_138 f) (nb078_wpp_notmem_0358) (nb078_wpp_notmem_0359 f) (TEnvFresh.consFresh (nb078_alpha_dummy_135) (nb078_alpha_dummy_136 f) (nb078_wpp_notmem_0360) (nb078_wpp_notmem_0361 f) (TEnvFresh.consFresh (nb078_alpha_dummy_090) (nb078_alpha_dummy_092 f) (nb078_wpp_notmem_0256) (nb078_wpp_notmem_0257 f) (TEnvFresh.consFresh (nb078_alpha_dummy_089) (nb078_alpha_dummy_091 f) (nb078_wpp_notmem_0258) (nb078_wpp_notmem_0259 f) (TEnvFresh.consFresh (nb078_alpha_dummy_093) (nb078_alpha_dummy_094 f) (nb078_wpp_notmem_0260) (nb078_wpp_notmem_0261 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0166) (nb078_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0020) (nb078_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0022) (nb078_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0024) (nb078_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0026) (nb078_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0028) (nb078_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0030) (nb078_wpp_notmem_0031 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0021 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0021 x y f)

theorem nb078_wpp_notmem_0362 : (nb078_alpha_dummy_147) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_147, fv_syn_c0] using (nb078_compact_fv_empty_0102)

theorem nb078_wpp_notmem_0363 (f : Var) : (nb078_alpha_dummy_150 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_150, fv_syn_c0] using (nb078_compact_fv_empty_0103 f)

theorem nb078_wpp_notmem_0364 : (nb078_alpha_dummy_146) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_146, fv_syn_c0] using (nb078_compact_fv_empty_0104)

theorem nb078_wpp_notmem_0365 (f : Var) : (nb078_alpha_dummy_149 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_149, fv_syn_c0] using (nb078_compact_fv_empty_0105 f)

theorem nb078_wpp_notmem_0366 : (nb078_alpha_dummy_145) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_145, fv_syn_c0] using (nb078_compact_fv_empty_0106)

theorem nb078_wpp_notmem_0367 (f : Var) : (nb078_alpha_dummy_148 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_148, fv_syn_c0] using (nb078_compact_fv_empty_0107 f)

theorem nb078_wpp_notmem_0368 : (nb078_alpha_dummy_143) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_143, fv_syn_c0] using (nb078_compact_fv_empty_0108)

theorem nb078_wpp_notmem_0369 (f : Var) : (nb078_alpha_dummy_144 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_144, fv_syn_c0] using (nb078_compact_fv_empty_0109 f)

theorem nb078_wpp_notmem_0370 : (nb078_alpha_dummy_139) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_139, fv_syn_c0] using (nb078_compact_fv_empty_0110)

theorem nb078_wpp_notmem_0371 (f : Var) : (nb078_alpha_dummy_141 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_141, fv_syn_c0] using (nb078_compact_fv_empty_0111 f)

theorem nb078_wpp_notmem_0372 : (nb078_alpha_dummy_140) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_140, fv_syn_c0] using (nb078_compact_fv_empty_0112)

theorem nb078_wpp_notmem_0373 (f : Var) : (nb078_alpha_dummy_142 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_142, fv_syn_c0] using (nb078_compact_fv_empty_0113 f)

theorem nb078_wpp_notmem_0374 : (nb078_alpha_dummy_132) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_132, fv_syn_c0] using (nb078_compact_fv_empty_0114)

theorem nb078_wpp_notmem_0375 (f : Var) : (nb078_alpha_dummy_134 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_134, fv_syn_c0] using (nb078_compact_fv_empty_0115 f)

theorem nb078_wpp_notmem_0376 : (nb078_alpha_dummy_131) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_131, fv_syn_c0] using (nb078_compact_fv_empty_0116)

theorem nb078_wpp_notmem_0377 (f : Var) : (nb078_alpha_dummy_133 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_133, fv_syn_c0] using (nb078_compact_fv_empty_0117 f)

theorem nb078_wpp_notmem_0378 : (nb078_alpha_dummy_137) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_137, fv_syn_c0] using (nb078_compact_fv_empty_0118)

theorem nb078_wpp_notmem_0379 (f : Var) : (nb078_alpha_dummy_138 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_138, fv_syn_c0] using (nb078_compact_fv_empty_0119 f)

theorem nb078_wpp_notmem_0380 : (nb078_alpha_dummy_135) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_135, fv_syn_c0] using (nb078_compact_fv_empty_0120)

theorem nb078_wpp_notmem_0381 (f : Var) : (nb078_alpha_dummy_136 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_136, fv_syn_c0] using (nb078_compact_fv_empty_0121 f)

theorem nb078_compact_envfresh_0022 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_147) (nb078_alpha_dummy_150 f) (nb078_wpp_notmem_0362) (nb078_wpp_notmem_0363 f) (TEnvFresh.consFresh (nb078_alpha_dummy_146) (nb078_alpha_dummy_149 f) (nb078_wpp_notmem_0364) (nb078_wpp_notmem_0365 f) (TEnvFresh.consFresh (nb078_alpha_dummy_145) (nb078_alpha_dummy_148 f) (nb078_wpp_notmem_0366) (nb078_wpp_notmem_0367 f) (TEnvFresh.consFresh (nb078_alpha_dummy_143) (nb078_alpha_dummy_144 f) (nb078_wpp_notmem_0368) (nb078_wpp_notmem_0369 f) (TEnvFresh.consFresh (nb078_alpha_dummy_139) (nb078_alpha_dummy_141 f) (nb078_wpp_notmem_0370) (nb078_wpp_notmem_0371 f) (TEnvFresh.consFresh (nb078_alpha_dummy_140) (nb078_alpha_dummy_142 f) (nb078_wpp_notmem_0372) (nb078_wpp_notmem_0373 f) (TEnvFresh.consFresh (nb078_alpha_dummy_132) (nb078_alpha_dummy_134 f) (nb078_wpp_notmem_0374) (nb078_wpp_notmem_0375 f) (TEnvFresh.consFresh (nb078_alpha_dummy_131) (nb078_alpha_dummy_133 f) (nb078_wpp_notmem_0376) (nb078_wpp_notmem_0377 f) (TEnvFresh.consFresh (nb078_alpha_dummy_137) (nb078_alpha_dummy_138 f) (nb078_wpp_notmem_0378) (nb078_wpp_notmem_0379 f) (TEnvFresh.consFresh (nb078_alpha_dummy_135) (nb078_alpha_dummy_136 f) (nb078_wpp_notmem_0380) (nb078_wpp_notmem_0381 f) (TEnvFresh.consFresh (nb078_alpha_dummy_090) (nb078_alpha_dummy_092 f) (nb078_wpp_notmem_0282) (nb078_wpp_notmem_0283 f) (TEnvFresh.consFresh (nb078_alpha_dummy_089) (nb078_alpha_dummy_091 f) (nb078_wpp_notmem_0284) (nb078_wpp_notmem_0285 f) (TEnvFresh.consFresh (nb078_alpha_dummy_093) (nb078_alpha_dummy_094 f) (nb078_wpp_notmem_0286) (nb078_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0188) (nb078_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0056) (nb078_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0058) (nb078_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0060) (nb078_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0062) (nb078_wpp_notmem_0063 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0064) (nb078_wpp_notmem_0065 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0066) (nb078_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0022 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0022 x y f)

theorem nb078_wpp_notmem_0382 : (nb078_alpha_dummy_143) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_143, fv_syn_cnnc] using (nb078_compact_fv_empty_0108)

theorem nb078_wpp_notmem_0383 (f : Var) : (nb078_alpha_dummy_144 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_144, fv_syn_cnnc] using (nb078_compact_fv_empty_0109 f)

theorem nb078_wpp_notmem_0384 : (nb078_alpha_dummy_139) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_139, fv_syn_cnnc] using (nb078_compact_fv_empty_0110)

theorem nb078_wpp_notmem_0385 (f : Var) : (nb078_alpha_dummy_141 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_141, fv_syn_cnnc] using (nb078_compact_fv_empty_0111 f)

theorem nb078_wpp_notmem_0386 : (nb078_alpha_dummy_140) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_140, fv_syn_cnnc] using (nb078_compact_fv_empty_0112)

theorem nb078_wpp_notmem_0387 (f : Var) : (nb078_alpha_dummy_142 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_142, fv_syn_cnnc] using (nb078_compact_fv_empty_0113 f)

theorem nb078_wpp_notmem_0388 : (nb078_alpha_dummy_132) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_132, fv_syn_cnnc] using (nb078_compact_fv_empty_0114)

theorem nb078_wpp_notmem_0389 (f : Var) : (nb078_alpha_dummy_134 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_134, fv_syn_cnnc] using (nb078_compact_fv_empty_0115 f)

theorem nb078_wpp_notmem_0390 : (nb078_alpha_dummy_131) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_131, fv_syn_cnnc] using (nb078_compact_fv_empty_0116)

theorem nb078_wpp_notmem_0391 (f : Var) : (nb078_alpha_dummy_133 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_133, fv_syn_cnnc] using (nb078_compact_fv_empty_0117 f)

theorem nb078_wpp_notmem_0392 : (nb078_alpha_dummy_137) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_137, fv_syn_cnnc] using (nb078_compact_fv_empty_0118)

theorem nb078_wpp_notmem_0393 (f : Var) : (nb078_alpha_dummy_138 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_138, fv_syn_cnnc] using (nb078_compact_fv_empty_0119 f)

theorem nb078_wpp_notmem_0394 : (nb078_alpha_dummy_135) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_135, fv_syn_cnnc] using (nb078_compact_fv_empty_0120)

theorem nb078_wpp_notmem_0395 (f : Var) : (nb078_alpha_dummy_136 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_136, fv_syn_cnnc] using (nb078_compact_fv_empty_0121 f)

theorem nb078_compact_envfresh_0023 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_143) (nb078_alpha_dummy_144 f) (nb078_wpp_notmem_0382) (nb078_wpp_notmem_0383 f) (TEnvFresh.consFresh (nb078_alpha_dummy_139) (nb078_alpha_dummy_141 f) (nb078_wpp_notmem_0384) (nb078_wpp_notmem_0385 f) (TEnvFresh.consFresh (nb078_alpha_dummy_140) (nb078_alpha_dummy_142 f) (nb078_wpp_notmem_0386) (nb078_wpp_notmem_0387 f) (TEnvFresh.consFresh (nb078_alpha_dummy_132) (nb078_alpha_dummy_134 f) (nb078_wpp_notmem_0388) (nb078_wpp_notmem_0389 f) (TEnvFresh.consFresh (nb078_alpha_dummy_131) (nb078_alpha_dummy_133 f) (nb078_wpp_notmem_0390) (nb078_wpp_notmem_0391 f) (TEnvFresh.consFresh (nb078_alpha_dummy_137) (nb078_alpha_dummy_138 f) (nb078_wpp_notmem_0392) (nb078_wpp_notmem_0393 f) (TEnvFresh.consFresh (nb078_alpha_dummy_135) (nb078_alpha_dummy_136 f) (nb078_wpp_notmem_0394) (nb078_wpp_notmem_0395 f) (TEnvFresh.consFresh (nb078_alpha_dummy_090) (nb078_alpha_dummy_092 f) (nb078_wpp_notmem_0302) (nb078_wpp_notmem_0303 f) (TEnvFresh.consFresh (nb078_alpha_dummy_089) (nb078_alpha_dummy_091 f) (nb078_wpp_notmem_0304) (nb078_wpp_notmem_0305 f) (TEnvFresh.consFresh (nb078_alpha_dummy_093) (nb078_alpha_dummy_094 f) (nb078_wpp_notmem_0306) (nb078_wpp_notmem_0307 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0204) (nb078_wpp_notmem_0205 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0086) (nb078_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0088) (nb078_wpp_notmem_0089 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0090) (nb078_wpp_notmem_0091 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0092) (nb078_wpp_notmem_0093 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0094) (nb078_wpp_notmem_0095 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0096) (nb078_wpp_notmem_0097 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
