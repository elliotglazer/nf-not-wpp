import NAR4C078C001Part038

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

noncomputable def nb078_split_alpha_0007 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_165)) (syn_cphi (Class.cv (nb078_alpha_dummy_132)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_165)) (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_166 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_166 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0129 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0129 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0159 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0157 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_132))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_134 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0132) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0133 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0131 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0024 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0137 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0135 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0139 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0137 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0135 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0139 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0025 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0143 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0143 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0147 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0147 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0131 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0026 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0131 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0131 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0026 x y f)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0129 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0129 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0159 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0157 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_132))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_134 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0132) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0133 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0132) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0133 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0131 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0024 x y f))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0137 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0135 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0139 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0137 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0135 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0140) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0138) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0139 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0025 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0143 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0144) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0145 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0142) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0143 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0147 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0148) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0149 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0146) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0147 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0131 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0026 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0131 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0130) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0131 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0026 x y f))))))))))))))))))))

theorem nb078_wpp_notmem_0414 : (nb078_alpha_dummy_163) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_163, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0124)

theorem nb078_wpp_notmem_0415 (f : Var) : (nb078_alpha_dummy_164 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_164, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0125 f)

theorem nb078_wpp_notmem_0416 : (nb078_alpha_dummy_132) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_132, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0114)

theorem nb078_wpp_notmem_0417 (f : Var) : (nb078_alpha_dummy_134 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_134, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0115 f)

theorem nb078_wpp_notmem_0418 : (nb078_alpha_dummy_131) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_131, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0116)

theorem nb078_wpp_notmem_0419 (f : Var) : (nb078_alpha_dummy_133 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_133, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0117 f)

theorem nb078_wpp_notmem_0420 : (nb078_alpha_dummy_161) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_161, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0126)

theorem nb078_wpp_notmem_0421 (f : Var) : (nb078_alpha_dummy_162 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_162, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0127 f)

theorem nb078_wpp_notmem_0422 : (nb078_alpha_dummy_135) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_135, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0120)

theorem nb078_wpp_notmem_0423 (f : Var) : (nb078_alpha_dummy_136 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_136, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0121 f)

theorem nb078_compact_envfresh_0027 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_163) (nb078_alpha_dummy_164 f) (nb078_wpp_notmem_0414) (nb078_wpp_notmem_0415 f) (TEnvFresh.consFresh (nb078_alpha_dummy_132) (nb078_alpha_dummy_134 f) (nb078_wpp_notmem_0416) (nb078_wpp_notmem_0417 f) (TEnvFresh.consFresh (nb078_alpha_dummy_131) (nb078_alpha_dummy_133 f) (nb078_wpp_notmem_0418) (nb078_wpp_notmem_0419 f) (TEnvFresh.consFresh (nb078_alpha_dummy_161) (nb078_alpha_dummy_162 f) (nb078_wpp_notmem_0420) (nb078_wpp_notmem_0421 f) (TEnvFresh.consFresh (nb078_alpha_dummy_135) (nb078_alpha_dummy_136 f) (nb078_wpp_notmem_0422) (nb078_wpp_notmem_0423 f) (TEnvFresh.consFresh (nb078_alpha_dummy_090) (nb078_alpha_dummy_092 f) (nb078_wpp_notmem_0336) (nb078_wpp_notmem_0337 f) (TEnvFresh.consFresh (nb078_alpha_dummy_089) (nb078_alpha_dummy_091 f) (nb078_wpp_notmem_0338) (nb078_wpp_notmem_0339 f) (TEnvFresh.consFresh (nb078_alpha_dummy_093) (nb078_alpha_dummy_094 f) (nb078_wpp_notmem_0340) (nb078_wpp_notmem_0341 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0234) (nb078_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0130) (nb078_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0132) (nb078_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0134) (nb078_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0136) (nb078_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0138) (nb078_wpp_notmem_0139 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0140) (nb078_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0027 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0027 x y f)

theorem nb078_compact_fv_empty_0128 : (nb078_alpha_dummy_183) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0424 : (nb078_alpha_dummy_183) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_183, fv_syn_c1c] using (nb078_compact_fv_empty_0128)

theorem nb078_compact_fv_empty_0129 (f : Var) : (nb078_alpha_dummy_186 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0425 (f : Var) : (nb078_alpha_dummy_186 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_186, fv_syn_c1c] using (nb078_compact_fv_empty_0129 f)

theorem nb078_compact_fv_empty_0130 : (nb078_alpha_dummy_182) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0426 : (nb078_alpha_dummy_182) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_182, fv_syn_c1c] using (nb078_compact_fv_empty_0130)

theorem nb078_compact_fv_empty_0131 (f : Var) : (nb078_alpha_dummy_185 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0427 (f : Var) : (nb078_alpha_dummy_185 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_185, fv_syn_c1c] using (nb078_compact_fv_empty_0131 f)

theorem nb078_compact_fv_empty_0132 : (nb078_alpha_dummy_181) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0428 : (nb078_alpha_dummy_181) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_181, fv_syn_c1c] using (nb078_compact_fv_empty_0132)

theorem nb078_compact_fv_empty_0133 (f : Var) : (nb078_alpha_dummy_184 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0429 (f : Var) : (nb078_alpha_dummy_184 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_184, fv_syn_c1c] using (nb078_compact_fv_empty_0133 f)

theorem nb078_compact_fv_empty_0134 : (nb078_alpha_dummy_179) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0430 : (nb078_alpha_dummy_179) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_179, fv_syn_c1c] using (nb078_compact_fv_empty_0134)

theorem nb078_compact_fv_empty_0135 (f : Var) : (nb078_alpha_dummy_180 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0431 (f : Var) : (nb078_alpha_dummy_180 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_180, fv_syn_c1c] using (nb078_compact_fv_empty_0135 f)

theorem nb078_compact_fv_empty_0136 : (nb078_alpha_dummy_175) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0432 : (nb078_alpha_dummy_175) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_175, fv_syn_c1c] using (nb078_compact_fv_empty_0136)

theorem nb078_compact_fv_empty_0137 (f : Var) : (nb078_alpha_dummy_177 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0433 (f : Var) : (nb078_alpha_dummy_177 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_177, fv_syn_c1c] using (nb078_compact_fv_empty_0137 f)

theorem nb078_compact_fv_empty_0138 : (nb078_alpha_dummy_176) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0434 : (nb078_alpha_dummy_176) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_176, fv_syn_c1c] using (nb078_compact_fv_empty_0138)

theorem nb078_compact_fv_empty_0139 (f : Var) : (nb078_alpha_dummy_178 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0435 (f : Var) : (nb078_alpha_dummy_178 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_178, fv_syn_c1c] using (nb078_compact_fv_empty_0139 f)

theorem nb078_compact_fv_empty_0140 : (nb078_alpha_dummy_168) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0436 : (nb078_alpha_dummy_168) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_168, fv_syn_c1c] using (nb078_compact_fv_empty_0140)

theorem nb078_compact_fv_empty_0141 (f : Var) : (nb078_alpha_dummy_170 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0437 (f : Var) : (nb078_alpha_dummy_170 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_170, fv_syn_c1c] using (nb078_compact_fv_empty_0141 f)

theorem nb078_compact_fv_empty_0142 : (nb078_alpha_dummy_167) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0438 : (nb078_alpha_dummy_167) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_167, fv_syn_c1c] using (nb078_compact_fv_empty_0142)

theorem nb078_compact_fv_empty_0143 (f : Var) : (nb078_alpha_dummy_169 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0439 (f : Var) : (nb078_alpha_dummy_169 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_169, fv_syn_c1c] using (nb078_compact_fv_empty_0143 f)

theorem nb078_compact_fv_empty_0144 : (nb078_alpha_dummy_173) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0440 : (nb078_alpha_dummy_173) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_173, fv_syn_c1c] using (nb078_compact_fv_empty_0144)

theorem nb078_compact_fv_empty_0145 (f : Var) : (nb078_alpha_dummy_174 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0441 (f : Var) : (nb078_alpha_dummy_174 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_174, fv_syn_c1c] using (nb078_compact_fv_empty_0145 f)

theorem nb078_compact_fv_empty_0146 : (nb078_alpha_dummy_171) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0442 : (nb078_alpha_dummy_171) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_171, fv_syn_c1c] using (nb078_compact_fv_empty_0146)

theorem nb078_compact_fv_empty_0147 (f : Var) : (nb078_alpha_dummy_172 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0443 (f : Var) : (nb078_alpha_dummy_172 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_172, fv_syn_c1c] using (nb078_compact_fv_empty_0147 f)

theorem nb078_compact_envfresh_0028 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182), (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)), ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_183) (nb078_alpha_dummy_186 f) (nb078_wpp_notmem_0424) (nb078_wpp_notmem_0425 f) (TEnvFresh.consFresh (nb078_alpha_dummy_182) (nb078_alpha_dummy_185 f) (nb078_wpp_notmem_0426) (nb078_wpp_notmem_0427 f) (TEnvFresh.consFresh (nb078_alpha_dummy_181) (nb078_alpha_dummy_184 f) (nb078_wpp_notmem_0428) (nb078_wpp_notmem_0429 f) (TEnvFresh.consFresh (nb078_alpha_dummy_179) (nb078_alpha_dummy_180 f) (nb078_wpp_notmem_0430) (nb078_wpp_notmem_0431 f) (TEnvFresh.consFresh (nb078_alpha_dummy_175) (nb078_alpha_dummy_177 f) (nb078_wpp_notmem_0432) (nb078_wpp_notmem_0433 f) (TEnvFresh.consFresh (nb078_alpha_dummy_176) (nb078_alpha_dummy_178 f) (nb078_wpp_notmem_0434) (nb078_wpp_notmem_0435 f) (TEnvFresh.consFresh (nb078_alpha_dummy_168) (nb078_alpha_dummy_170 f) (nb078_wpp_notmem_0436) (nb078_wpp_notmem_0437 f) (TEnvFresh.consFresh (nb078_alpha_dummy_167) (nb078_alpha_dummy_169 f) (nb078_wpp_notmem_0438) (nb078_wpp_notmem_0439 f) (TEnvFresh.consFresh (nb078_alpha_dummy_173) (nb078_alpha_dummy_174 f) (nb078_wpp_notmem_0440) (nb078_wpp_notmem_0441 f) (TEnvFresh.consFresh (nb078_alpha_dummy_171) (nb078_alpha_dummy_172 f) (nb078_wpp_notmem_0442) (nb078_wpp_notmem_0443 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0166) (nb078_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0020) (nb078_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0022) (nb078_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0024) (nb078_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0026) (nb078_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0028) (nb078_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0030) (nb078_wpp_notmem_0031 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0028 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182), (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)), ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0028 x y f)

theorem nb078_wpp_notmem_0444 : (nb078_alpha_dummy_183) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_183, fv_syn_c0] using (nb078_compact_fv_empty_0128)

theorem nb078_wpp_notmem_0445 (f : Var) : (nb078_alpha_dummy_186 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_186, fv_syn_c0] using (nb078_compact_fv_empty_0129 f)

theorem nb078_wpp_notmem_0446 : (nb078_alpha_dummy_182) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_182, fv_syn_c0] using (nb078_compact_fv_empty_0130)

theorem nb078_wpp_notmem_0447 (f : Var) : (nb078_alpha_dummy_185 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_185, fv_syn_c0] using (nb078_compact_fv_empty_0131 f)

theorem nb078_wpp_notmem_0448 : (nb078_alpha_dummy_181) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_181, fv_syn_c0] using (nb078_compact_fv_empty_0132)

theorem nb078_wpp_notmem_0449 (f : Var) : (nb078_alpha_dummy_184 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_184, fv_syn_c0] using (nb078_compact_fv_empty_0133 f)

theorem nb078_wpp_notmem_0450 : (nb078_alpha_dummy_179) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_179, fv_syn_c0] using (nb078_compact_fv_empty_0134)

theorem nb078_wpp_notmem_0451 (f : Var) : (nb078_alpha_dummy_180 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_180, fv_syn_c0] using (nb078_compact_fv_empty_0135 f)

theorem nb078_wpp_notmem_0452 : (nb078_alpha_dummy_175) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_175, fv_syn_c0] using (nb078_compact_fv_empty_0136)

theorem nb078_wpp_notmem_0453 (f : Var) : (nb078_alpha_dummy_177 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_177, fv_syn_c0] using (nb078_compact_fv_empty_0137 f)

theorem nb078_wpp_notmem_0454 : (nb078_alpha_dummy_176) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_176, fv_syn_c0] using (nb078_compact_fv_empty_0138)

theorem nb078_wpp_notmem_0455 (f : Var) : (nb078_alpha_dummy_178 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_178, fv_syn_c0] using (nb078_compact_fv_empty_0139 f)

theorem nb078_wpp_notmem_0456 : (nb078_alpha_dummy_168) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_168, fv_syn_c0] using (nb078_compact_fv_empty_0140)

theorem nb078_wpp_notmem_0457 (f : Var) : (nb078_alpha_dummy_170 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_170, fv_syn_c0] using (nb078_compact_fv_empty_0141 f)

theorem nb078_wpp_notmem_0458 : (nb078_alpha_dummy_167) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_167, fv_syn_c0] using (nb078_compact_fv_empty_0142)

theorem nb078_wpp_notmem_0459 (f : Var) : (nb078_alpha_dummy_169 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_169, fv_syn_c0] using (nb078_compact_fv_empty_0143 f)

theorem nb078_wpp_notmem_0460 : (nb078_alpha_dummy_173) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_173, fv_syn_c0] using (nb078_compact_fv_empty_0144)

theorem nb078_wpp_notmem_0461 (f : Var) : (nb078_alpha_dummy_174 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_174, fv_syn_c0] using (nb078_compact_fv_empty_0145 f)

theorem nb078_wpp_notmem_0462 : (nb078_alpha_dummy_171) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_171, fv_syn_c0] using (nb078_compact_fv_empty_0146)

theorem nb078_wpp_notmem_0463 (f : Var) : (nb078_alpha_dummy_172 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_172, fv_syn_c0] using (nb078_compact_fv_empty_0147 f)

theorem nb078_compact_envfresh_0029 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182), (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)), ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_183) (nb078_alpha_dummy_186 f) (nb078_wpp_notmem_0444) (nb078_wpp_notmem_0445 f) (TEnvFresh.consFresh (nb078_alpha_dummy_182) (nb078_alpha_dummy_185 f) (nb078_wpp_notmem_0446) (nb078_wpp_notmem_0447 f) (TEnvFresh.consFresh (nb078_alpha_dummy_181) (nb078_alpha_dummy_184 f) (nb078_wpp_notmem_0448) (nb078_wpp_notmem_0449 f) (TEnvFresh.consFresh (nb078_alpha_dummy_179) (nb078_alpha_dummy_180 f) (nb078_wpp_notmem_0450) (nb078_wpp_notmem_0451 f) (TEnvFresh.consFresh (nb078_alpha_dummy_175) (nb078_alpha_dummy_177 f) (nb078_wpp_notmem_0452) (nb078_wpp_notmem_0453 f) (TEnvFresh.consFresh (nb078_alpha_dummy_176) (nb078_alpha_dummy_178 f) (nb078_wpp_notmem_0454) (nb078_wpp_notmem_0455 f) (TEnvFresh.consFresh (nb078_alpha_dummy_168) (nb078_alpha_dummy_170 f) (nb078_wpp_notmem_0456) (nb078_wpp_notmem_0457 f) (TEnvFresh.consFresh (nb078_alpha_dummy_167) (nb078_alpha_dummy_169 f) (nb078_wpp_notmem_0458) (nb078_wpp_notmem_0459 f) (TEnvFresh.consFresh (nb078_alpha_dummy_173) (nb078_alpha_dummy_174 f) (nb078_wpp_notmem_0460) (nb078_wpp_notmem_0461 f) (TEnvFresh.consFresh (nb078_alpha_dummy_171) (nb078_alpha_dummy_172 f) (nb078_wpp_notmem_0462) (nb078_wpp_notmem_0463 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0188) (nb078_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0056) (nb078_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0058) (nb078_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0060) (nb078_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0062) (nb078_wpp_notmem_0063 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0064) (nb078_wpp_notmem_0065 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0066) (nb078_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0029 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182), (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)), ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0029 x y f)

theorem nb078_wpp_notmem_0464 : (nb078_alpha_dummy_179) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_179, fv_syn_cnnc] using (nb078_compact_fv_empty_0134)

theorem nb078_wpp_notmem_0465 (f : Var) : (nb078_alpha_dummy_180 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_180, fv_syn_cnnc] using (nb078_compact_fv_empty_0135 f)

theorem nb078_wpp_notmem_0466 : (nb078_alpha_dummy_175) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_175, fv_syn_cnnc] using (nb078_compact_fv_empty_0136)

theorem nb078_wpp_notmem_0467 (f : Var) : (nb078_alpha_dummy_177 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_177, fv_syn_cnnc] using (nb078_compact_fv_empty_0137 f)

theorem nb078_wpp_notmem_0468 : (nb078_alpha_dummy_176) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_176, fv_syn_cnnc] using (nb078_compact_fv_empty_0138)

theorem nb078_wpp_notmem_0469 (f : Var) : (nb078_alpha_dummy_178 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_178, fv_syn_cnnc] using (nb078_compact_fv_empty_0139 f)

theorem nb078_wpp_notmem_0470 : (nb078_alpha_dummy_168) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_168, fv_syn_cnnc] using (nb078_compact_fv_empty_0140)

theorem nb078_wpp_notmem_0471 (f : Var) : (nb078_alpha_dummy_170 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_170, fv_syn_cnnc] using (nb078_compact_fv_empty_0141 f)

theorem nb078_wpp_notmem_0472 : (nb078_alpha_dummy_167) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_167, fv_syn_cnnc] using (nb078_compact_fv_empty_0142)

theorem nb078_wpp_notmem_0473 (f : Var) : (nb078_alpha_dummy_169 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_169, fv_syn_cnnc] using (nb078_compact_fv_empty_0143 f)

theorem nb078_wpp_notmem_0474 : (nb078_alpha_dummy_173) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_173, fv_syn_cnnc] using (nb078_compact_fv_empty_0144)

theorem nb078_wpp_notmem_0475 (f : Var) : (nb078_alpha_dummy_174 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_174, fv_syn_cnnc] using (nb078_compact_fv_empty_0145 f)

theorem nb078_wpp_notmem_0476 : (nb078_alpha_dummy_171) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_171, fv_syn_cnnc] using (nb078_compact_fv_empty_0146)

theorem nb078_wpp_notmem_0477 (f : Var) : (nb078_alpha_dummy_172 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_172, fv_syn_cnnc] using (nb078_compact_fv_empty_0147 f)

theorem nb078_compact_envfresh_0030 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_179) (nb078_alpha_dummy_180 f) (nb078_wpp_notmem_0464) (nb078_wpp_notmem_0465 f) (TEnvFresh.consFresh (nb078_alpha_dummy_175) (nb078_alpha_dummy_177 f) (nb078_wpp_notmem_0466) (nb078_wpp_notmem_0467 f) (TEnvFresh.consFresh (nb078_alpha_dummy_176) (nb078_alpha_dummy_178 f) (nb078_wpp_notmem_0468) (nb078_wpp_notmem_0469 f) (TEnvFresh.consFresh (nb078_alpha_dummy_168) (nb078_alpha_dummy_170 f) (nb078_wpp_notmem_0470) (nb078_wpp_notmem_0471 f) (TEnvFresh.consFresh (nb078_alpha_dummy_167) (nb078_alpha_dummy_169 f) (nb078_wpp_notmem_0472) (nb078_wpp_notmem_0473 f) (TEnvFresh.consFresh (nb078_alpha_dummy_173) (nb078_alpha_dummy_174 f) (nb078_wpp_notmem_0474) (nb078_wpp_notmem_0475 f) (TEnvFresh.consFresh (nb078_alpha_dummy_171) (nb078_alpha_dummy_172 f) (nb078_wpp_notmem_0476) (nb078_wpp_notmem_0477 f) (TEnvFresh.consFresh (nb078_alpha_dummy_011) (nb078_alpha_dummy_014 f) (nb078_wpp_notmem_0204) (nb078_wpp_notmem_0205 f) (TEnvFresh.consFresh (nb078_alpha_dummy_010) (nb078_alpha_dummy_013 f) (nb078_wpp_notmem_0086) (nb078_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb078_alpha_dummy_009) (nb078_alpha_dummy_012 f) (nb078_wpp_notmem_0088) (nb078_wpp_notmem_0089 f) (TEnvFresh.consFresh (nb078_alpha_dummy_015) (nb078_alpha_dummy_016 f) (nb078_wpp_notmem_0090) (nb078_wpp_notmem_0091 f) (TEnvFresh.consFresh (nb078_alpha_dummy_007) (nb078_alpha_dummy_008 f) (nb078_wpp_notmem_0092) (nb078_wpp_notmem_0093 f) (TEnvFresh.consFresh (nb078_alpha_dummy_005) (nb078_alpha_dummy_006 f) (nb078_wpp_notmem_0094) (nb078_wpp_notmem_0095 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0096) (nb078_wpp_notmem_0097 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb078_wpp_refl_0030 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0030 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
